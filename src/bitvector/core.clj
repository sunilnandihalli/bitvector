(ns bitvector.core
  (:require [clojure.java.io :as io]
            [clojure.contrib.combinatorics :as comb]
            [clojure.contrib.generic.math-functions :as mfn]
            [clojure.contrib.profile :as prf]
            [bitvector.tree-utils :as tr]
            [bitvector.priority-map :as pm])
  (:import [java.io BufferedReader BufferedWriter FileReader])
  (:use bitvector.debug clojure.inspector bitvector.log-utils))

(def ^{:doc "probability of mutation during cloning"} mutation-probability 0.2)
(def ^{:doc "log of the mutation probability"} log-p (mfn/log mutation-probability))
(def log-1-p (mfn/log (- 1 mutation-probability)))
(def log-1-p-over-p (- log-1-p log-p))

(defn abs [x] (if (< x 0) (- x) x))
           
(defn hash-calculating-func [hash-length dimension-d]
  "a function to return a randomly generated locality sensitive hash function as described in Motwani et. al."
  (let [ids (take hash-length (shuffle (range dimension-d)))]
    (fn [bv] (reduce (fn [hash [hash-loc-id bv-pos-id]]
                       (if (aget bv bv-pos-id)
                         (bit-set hash hash-loc-id) hash)) 0 (map-indexed vector ids)))))
                        
(defn bit-dist [{memory :distance-memory bit-vectors :bit-vectors} [& [i j]]]
  "hamming distance between the the bitvectors i and j"
  (prf/prof :bit-dist (let [bit-dist-help (fn [a b]
                                            (loop [[fa & ra] a [fb & rb] b d 0]
                                              (if (not (nil? fa)) (recur ra rb (if (not= fa fb) (inc d) d)) d)))
                            get-dist (fn [i j] (if-let [[_ v] (find @memory [i j])] v
                                                       (let [v (bit-dist-help (bit-vectors i) (bit-vectors j))]
                                                         (swap! memory #(assoc % [i j] v)) v)))]                   
                        (cond (= i j) 0 (> i j) (get-dist i j) :else (get-dist j i)))))

(defn add-edge-to-graph [mst [start end]]
  "adds an edge to the graph"
  (-> mst (update-in [start] #(if % (conj % end) #{end})) (update-in [end] #(if % (conj % start) #{start}))))

(defn update-disjoint-mst-coll [{:keys [disjoint-mst-coll nodes-to-mst-id-map] :as mst} [& [s e :as edge]]]
  "at any stage, we maintain a collection of disjoint-msts and this function updates it by adding the edge [s e] to it joining two msts to get 1 mst if need be"
  (let [[tr-id1 tr-id2 :as tree-ids] (keep nodes-to-mst-id-map edge)]
    (if (and tr-id1 tr-id2 (= tr-id1 tr-id2)) mst
        (let [[tr1 tr2] (map disjoint-mst-coll tree-ids)
              n-tr-ids (count tree-ids)
              new-tree (-> (case n-tr-ids 0 {} 1 tr1 2 (into tr1 tr2)) (add-edge-to-graph [s e]))
              new-tree-id (case n-tr-ids 
                                0 (-> (rseq disjoint-mst-coll) ffirst inc-or-init)
                                1 (first tree-ids)
                                2 (if (> (count tr1) (count tr2)) tr-id1 tr-id2))
              new-disjoint-mst-coll (-> (reduce dissoc disjoint-mst-coll tree-ids) (assoc new-tree-id new-tree))
              assign-new-tree-id #(assoc %1 %2 new-tree-id)
              new-nodes-to-mst-id-map (thrush-with-sym [x]
                                        (reduce assign-new-tree-id nodes-to-mst-id-map edge)
                                        (condp = new-tree-id ;; can simplify .. written this way for performance...
                                            tr-id1 (reduce assign-new-tree-id x (keys tr2))
                                            tr-id2 (reduce assign-new-tree-id x (keys tr1)) x))]
          {:disjoint-mst-coll new-disjoint-mst-coll :nodes-to-mst-id-map new-nodes-to-mst-id-map}))))     
    
(defn mst-prim-edges [edges f {:keys [nodes-to-mst-id-map] :as mst}]
  "this function takes a collection edges all of whose end points collide equal number of times when hashed, it is assumed that all edges whose end points collide more when hashed are necessarily shorter in the hamming distance sense even though it may not be true in reality"
  (let [all-potential-edges (thrush-with-sym [x] edges
                              (filter #(let [[tr-id1 tr-id2] (map nodes-to-mst-id-map %)]
                                         (or (not (and tr-id1 tr-id2)) (not= tr-id1 tr-id2)))  x)
                              (map (fn [cur-edge] {(f cur-edge) (list cur-edge)}) x)
                              (apply merge-with into (sorted-map) x))]
    (loop [[[cur-dist cur-dist-edge-set :as cur-dist-edge-set-pair] & rest-of-dist-edge-set-pairs :as all-dist-edge-set-pairs] (seq all-potential-edges)
           [cur-dist-edge & rest-of-cur-dist-edges] nil cur-mst mst]
      (cond
       cur-dist-edge (recur all-dist-edge-set-pairs rest-of-cur-dist-edges (update-disjoint-mst-coll cur-mst cur-dist-edge))
       cur-dist-edge-set-pair (recur rest-of-dist-edge-set-pairs (seq cur-dist-edge-set) cur-mst)
       :else cur-mst))))
;;---------------------------------------------------------------------
(defn mst-prim-with-prioritized-edges [{:keys [prioritized-edges] cnt :count :as bv-stuff}]
  "calculate an approximate minimum spanning tree assuming that edges whose end points have the most collisions are necessarily shorter in terms of hamming distance than the ones whose edges whose endpoints collide fewer number of times"
  (let [edge-cost #(bit-dist bv-stuff %)
        {:keys [disjoint-mst-coll nodes-to-mst-id-map] :as mst}
        (loop [cur-mst {:disjoint-mst-coll (sorted-map) :nodes-to-mst-id-map {}}]
          (if-not edge-set-pairs-available cur-mst
                  (recur remaining-priority-edge-set-pairs (mst-prim-edges cur-equal-priority-edge-set edge-cost cur-mst))))]
    (if (= 1 (count disjoint-mst-coll)) (second (first disjoint-mst-coll))
        (do (display mst) (throw (Exception. "disjoint-pieces-found-in-mst"))))))
      
(defn optimize-root-id [{:keys [count bit-vectors] :as bv-stuff} gr]
  "optimize root id such that the permutations of the clonings needed to create the given tree is maximized"
  (let [{:keys [opt-root-id log-num-ways all-root-log-num-ways]} (tr/most-probable-root-for-a-given-tree gr)
        total-parent-child-dist (reduce (fn [s edge] (+ s (bit-dist bv-stuff edge))) 0 (prf/prof :edges-in-prufer-order (tr/edges-in-prufer-order gr)))
        log-parent-child-probability (log-mult (log-pow log-p total-parent-child-dist) (log-pow log-1-p (- (* count count) total-parent-child-dist)))
        total-quality (log-mult log-num-ways log-parent-child-probability)]
    (self-keyed-map log-num-ways log-parent-child-probability all-root-log-num-ways total-quality opt-root-id))) 

(defn write-genealogy
  "output the genealogy in the specified format"
  ([genealogy out-fname]
     (let [parents (apply str (interpose "\n" (vals (into (sorted-map) genealogy))))]
       (spit out-fname parents)))
  ([genealogy] (write-genealogy genealogy "parents.out")))
                       
(defn find-good-tree [{:keys [prioritized-edges] :as bv-stuff}]
  (let [minimum-spanning-free-tree (mst-prim-with-priority-edges bv-stuff prioritized-edges)
        {:keys [opt-root-id] :as sol-quality} (optimize-root-id bv-stuff minimum-spanning-free-tree)
        genealogy (tr/rooted-acyclic-graph-to-genealogy [minimum-spanning-free-tree opt-root-id])]
    (self-keyed-map sol-quality genealogy)))

(defn add-an-extra-hash-func [{:keys [bit-vectors hash-length number-of-hashes prioritized-edges tried-edges]
                               :or {prioritized-edges (pm/priority-map-by >) number-of-hashes 0 tried-edges #{}} cnt :count :as bv-stuff}]
  (let [new-hash-func (hash-calculating-func hash-length cnt)
        hash-buckets (persistent! (reduce (fn [cur-hash-buckets [id bv]] (non-std-update! cur-hash-buckets (new-hash-func bv) #(conj % id))) (transient {}) bit-vectors))
        new-prioritized-edges (reduce (fn [cur-prioritized-edges [hash-val bvs-with-same-hash]]
                                        (reduce (fn [cur-cur-probable-edges e]
                                                  (let [se (set e)]
                                                    (if-not (tried-edges se)
                                                      (update-in cur-cur-probable-edges [se] inc-or-init) cur-cur-probable-edges)))
                                                cur-probable-edges (comb/combinations bvs-with-same-hash 2))) prioritized-edges hash-buckets)]
    (assoc bv-stuff :prioritized-edges new-prioritized-edges :number-of-hashes (inc number-of-hashes))))

(defn add-n-extra-hash-funcs [bv-stuff n]
  (persistent! (reduce (fn [cur-bv-stuff _] (add-an-extra-hash-func cur-bv-stuff)) (transient bv-stuff) (range n))))

(defn calc-hashes-and-hash-fns [{:keys [bit-vectors] cnt :count :as bv-stuff} & {:keys [approximation-factor theta-const hash-length number-of-hashes]
                                                                                 :or {approximation-factor 4 theta-const 2}}]
  "calculate the hash functions and store the bit-vector ids in the corresponding buckets"
  (let [number-of-hashes (or number-of-hashes (* theta-const (mfn/pow cnt (/ 1 approximation-factor))))
        hash-length (or hash-length (/ number-of-hashes theta-const))]
    (add-n-extra-hash-funcs (assoc bv-stuff :hash-length hash-length) number-of-hashes)))

(defn read-bit-vectors [fname]
  "read the bit vectors from the file"
  (let [d (time (with-open [rdr (clojure.java.io/reader fname)]
                  (->> (line-seq rdr) (map-indexed #(vector %1 (boolean-array (map {\0 false \1 true} %2)))) (into {}))))
        n (count d) dist-memory (atom {})]
    {:distance-memory dist-memory :bit-vectors d :count n}))

(defn read-bit-vector-solution [fname]
  "read the sample solution from the file fnam"
  (time (with-open [rdr (clojure.java.io/reader fname)]
          (->> (line-seq rdr) (filter seq)
               (map-indexed #(vector %1 (read-string %2)))
               (into (sorted-map))))))

(defn add-edge-to-tree-ensuring-resulting-tree-is-better-than-original [{:keys [genealogy tried-edges] :as bv-stuff :or {tried-edges #{}}} [& [s e] :as new-edge]]
  {:pre [(set? new-edge) tried-edges genealogy]}
  (if (tried-edges new-edge)  bv-stuff
      (let [dist (partial bit-dist bv-stuff)
            path-between-end-points-of-new-edge (loop [cur-s s s-path [s]]
                                                  (let [cur-parent-s (genealogy cur-s)]
                                                    (condp = cur-parent-s
                                                        -1 (loop [cur-e e e-path [e]]
                                                             (let [cur-parent-e (genealogy cur-e)]
                                                               (condp = cur-parent-e
                                                                   -1 [s-path e-path] s [nil (conj e-path s)]
                                                                   (recur cur-parent-e (cons cur-parent-e e-path)))))
                                                        e [(conj s-path e) nil]
                                                        (recur cur-parent-s (conj s-path cur-parent-s)))))
            [start-list end-list :as path-edge-list] (map #(partition 2 1 %) path-between-end-points-of-new-edge)
            [min-edge min-dist new-edge-end-id] (min-key second (mapcat #(map (fn [edg] [edg (dist edg) %2]) %1) path-edge-list (range)))
            new-edge-dist (dist new-edge)
            new-tried-edges (conj tried-edges new-edge)
            update-genealogy (fn []
                               (persistent! (let [oriented-edge (case new-edge-end-id 0 new-edge 1 (reverse new-edge))]
                                              (reduce (fn [cur-genealogy [child parent]] (assoc! cur-genealogy child parent)) (transient genealogy)
                                                      (cons oriented-edge (take-while #(not= min-edge %) (path-edge-list new-edge-end-id)))))))]
        (-> (if (< new-edge-dist min-dist)
              (assoc bv-stuff :genealogy (update-genealogy)) bv-stuff)
            (assoc :tried-edges new-tried-edges)))))

(defn solution-quality [bv-stuff genealogy]
  "estimate the quality of given genealogy with respect to the bitvectors from bv-stuff"
  (->> (tr/genealogy-to-rooted-acyclic-graph genealogy)
       :acyclic-graph
       (optimize-root-id bv-stuff)))

(defn solve [& {:keys [fname solution-fname sample-solution n-increments delta-n-hashes]
                :or {fname "/home/github/bitvector/data/bitvectors-genes.data.small"
                     n-increments 5 delta-n-hashes 5}}]
  (let [solution-fname (if solution-fname solution-fname (str fname ".my-parents"))
        bv (prf/prof :read (read-bit-vectors fname))
        sample-solution-quality (if sample-solution (prf/prof :sample-solution-quality (solution-quality bv (read-bit-vector-solution sample-solution))))
        bv-stuff (prf/prof :calc-hashes (calc-hashes-and-hash-fns bv :approximation-factor 4))]
    (display sample-solution-quality)
    (loop [i-increments 0 cur-bv-stuff bv-stuff sol-qualities nil]
      (let [new-bv-stuff (prf/prof :add-hashes (add-n-extra-hash-funcs cur-bv-stuff delta-n-hashes))
            {:keys [sol-quality genealogy]} (prf/prof :find-good-tree (find-good-tree new-bv-stuff))]
        (write-genealogy genealogy (str solution-fname i-increments))
        (clojure.pprint/pprint (dissoc sol-quality :all-root-log-num-ways))
        (if (< i-increments n-increments) (recur (inc i-increments) new-bv-stuff (conj sol-qualities sol-quality))
            (let [reduced-sol-qualities (map #(dissoc % :all-root-log-num-ways) sol-qualities)]
                  (display reduced-sol-qualities genealogy)))))))

#_(time (solve :fname "/home/github/bitvector/data/bitvectors-genes.data.small"
               :sample-solution "/home/github/bitvector/data/bitvectors-parents.data.small.txt"))
#_(prf/profile (time (solve :fname "/home/github/bitvector/data/bitvectors-genes.data.small"
                            :sample-solution "/home/github/bitvector/data/bitvectors-parents.data.small.txt")))
#_(prf/profile (time (solve :fname "/home/github/bitvector/data/bitvectors-genes.data.large")))


(defn generate-random-bit-vector-set [n]
  (let [d (->> (fn [] (boolean-array (repeatedly n #({0 false 1 true} (rand-int 2))))) (repeatedly n)  into-array)
        dist-memory {}]
    {:distance-memory dist-memory :bit-vectors d :count n}))

(defn generate-input-problem [n]
  (let [clone (fn [parent mut-prob] (boolean-array (map #(if (< (rand) mut-prob) (not %) %) parent)))
        bit-vectors (reduce (fn [population id] (into population {id (clone (population (rand-int (count population))) mutation-probability)}))
                            {0 (boolean-array (repeatedly n #({0 false 1 true} (rand-int 2))))} (range 1 n))
        dist-memory (atom {})]
    {:distance-memory dist-memory :bit-vectors bit-vectors :count n}))

(defn solve-random
  ([out-fname] (let [bv-stuff (-> (generate-input-problem 10) (calc-hashes-and-hash-fns :approximation-factor 4))]
                 (write-genealogy (find-good-tree bv-stuff) out-fname)))
  ([] (solve "parents.out")))
