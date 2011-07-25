(ns bitvector.core
  (:require [clojure.java.io :as io]
            [clojure.contrib.combinatorics :as comb]
            [clojure.data.finger-tree :as ft]
            [clojure.contrib.generic.math-functions :as mfn]
            [clojure.contrib.profile :as prf]
            [bitvector.tree-utils :as tr])            
  (:import [java.io BufferedReader BufferedWriter FileReader])
  (:use iterate bitvector.debug clojure.inspector bitvector.log-utils))

(def ^{:doc "probability of mutation during cloning"} mutation-probability 0.2)
(def ^{:doc "log of the mutation probability"} log-p (mfn/log mutation-probability))
(def log-1-p (mfn/log (- 1 mutation-probability)))
(def log-1-p-over-p (- log-1-p log-p))

(defn abs [x] (if (< x 0) (- x) x))

(defn-memoized log-parent-child-probability [bit-cnt dist]
  "probability that two node which are bit-dist apart have a parent child relationship between them"
  (log-mult (log-pow log-p dist) (log-pow log-1-p (- bit-cnt dist))))
           
(defn hash-calculating-func [hash-length dimension-d]
  "a function to return a randomly generated locality sensitive hash function as described in Motwani et. al."
  (let [ids (take hash-length (shuffle (range dimension-d)))]
    (fn [bv] (reduce (fn [hash [hash-loc-id bv-pos-id]]
                       (if (aget bv bv-pos-id)
                         (bit-set hash hash-loc-id) hash)) 0 (map-indexed vector ids)))))

(defn all-probable-edges [{:keys [bv-hash-buckets] :as bv-stuff}]
  "returns a map from the edges which are obtained by taking all possible elements two at a time from each bucket"
  (loop [[[_ cur-hash-buckets] & rest-of-hash-buckets :as all-remaining-hash-buckets] (seq bv-hash-buckets)
         [[_ cur-bucket-nodes] & rest-of-hash-buckets-of-nodes :as w] nil
         pb-edges (transient {})]
    (cond
     cur-bucket-nodes (recur all-remaining-hash-buckets rest-of-hash-buckets-of-nodes
                             (loop [[e & rest-of-es :as all-es] (comb/combinations cur-bucket-nodes 2) pb-edges pb-edges]
                               (if-not e pb-edges
                                       (recur rest-of-es (non-std-update! pb-edges (set e) inc-or-init)))))
     cur-hash-buckets (recur rest-of-hash-buckets (seq cur-hash-buckets) pb-edges)
     :else (persistent! pb-edges))))
                        
(defn bit-dist [{memory :distance-memory bit-vectors :bit-vectors} [& [i j]]]
  "hamming distance between the the bitvectors i and j"
  (prf/prof :bit-dist (let [bit-dist-help (fn [a b]
                                            (loop [[fa & ra] a [fb & rb] b d 0]
                                              (if (not (nil? fa)) (recur ra rb (if (not= fa fb) (inc d) d)) d)))
                            get-dist (fn [i j] (if-let [[_ v] (find @memory [i j])] v
                                                       (let [v (bit-dist-help (bit-vectors i) (bit-vectors j))]
                                                         (swap! memory #(assoc % [i j] v)) v)))]                   
                        (cond (= i j) 0 (> i j) (get-dist i j) :else (get-dist j i)))))

(defn map-of-probable-edges [{:keys [bv-hash-buckets] :as bv-stuff}]
  "this function returns a map of edges to the number of times its end points collide when hashed using locality sensitive hashing"
  (let [probable-edges (all-probable-edges bv-stuff)
        trnsnt-n-collisions-2-trnsnt-edgset-map (loop [[[edge n-hash-collisions :as edge-pair] & rest-of-edge-collision-pairs] (seq probable-edges)
                                                       n-collision-edges-map (transient {})]
                                                  (if-not edge-pair n-collision-edges-map
                                                          (recur rest-of-edge-collision-pairs
                                                                 (non-std-update! n-collision-edges-map n-hash-collisions #(if % (conj! % edge) (transient [edge]))))))]
    (reduce (fn [persistent-sorted-map [n-hash-collisions transient-edge-set]]
              (assoc persistent-sorted-map n-hash-collisions (persistent! transient-edge-set)))
            (sorted-map-by >) (persistent! trnsnt-n-collisions-2-trnsnt-edgset-map))))    

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

(defn mst-prim-with-priority-edges [{cnt :count :as bv-stuff} probable-edge-map]
  "calculate an approximate minimum spanning tree assuming that edges whose end points have the most collisions are necessarily shorter in terms of hamming distance than the ones whose edges whose endpoints collide fewer number of times"
  (let [pb-edg-map (ensure-sortedness probable-edge-map)
        edge-cost #(bit-dist bv-stuff %)
        {:keys [disjoint-mst-coll nodes-to-mst-id-map] :as mst}
        (loop [[[cur-edge-priority cur-equal-priority-edge-set :as edge-set-pairs-available] & remaining-priority-edge-set-pairs] (seq pb-edg-map)
               cur-mst {:disjoint-mst-coll (sorted-map) :nodes-to-mst-id-map {}}]
          (if-not edge-set-pairs-available cur-mst
                  (recur remaining-priority-edge-set-pairs (mst-prim-edges cur-equal-priority-edge-set edge-cost cur-mst))))]
    (if (= 1 (count disjoint-mst-coll)) (second (first disjoint-mst-coll))
        (do (display mst) (throw (Exception. "disjoint-pieces-found-in-mst"))))))
      
(defn-memoized log-probability-of-bv [r n]
  "define a memoized version of the function which calculates the probability of given pair of bit vectors having parent-child relation ship"
  (log-mult (log-pow log-p r) (log-pow log-1-p (- n r))))

(defn optimize-root-id [{:keys [count bit-vectors] :as bv-stuff} gr]
  "optimize root id such that the permutations of the clonings needed to create the given tree is maximized"
  (let [{:keys [opt-root-id log-num-ways all-root-log-num-ways]} (tr/most-probable-root-for-a-given-tree gr)
        log-parent-child-probability (reduce + (map (fn [[i j]]
                                                      (let [dist (bit-dist bv-stuff [i j])]
                                                        (log-probability-of-bv dist count))) (prf/prof :edges-in-prufer-order (tr/edges-in-prufer-order gr))))
        total-quality (log-mult log-num-ways log-parent-child-probability)]
    (self-keyed-map log-num-ways log-parent-child-probability all-root-log-num-ways total-quality opt-root-id))) 

(defn write-genealogy
  "output the genealogy in the specified format"
  ([genealogy out-fname]
     (let [parents (apply str (interpose "\n" (vals (into (sorted-map) genealogy))))]
       (spit out-fname parents)))
  ([genealogy] (write-genealogy genealogy "parents.out")))
                       
(defn find-good-tree [bv-stuff]
  (let [probable-edges (map-of-probable-edges bv-stuff)
        minimum-spanning-free-tree (mst-prim-with-priority-edges bv-stuff probable-edges)
        {:keys [opt-root-id all-root-log-num-ways] :as sol-quality} (optimize-root-id bv-stuff minimum-spanning-free-tree)
        genealogy (tr/rooted-acyclic-graph-to-genealogy [minimum-spanning-free-tree opt-root-id])]
    (display sol-quality minimum-spanning-free-tree genealogy)
    genealogy))
           
(defn calc-hashes-and-hash-fns [{:keys [bit-vectors] cnt :count :as bv-stuff} & {:keys [approximation-factor theta-const hash-length number-of-hashes]
                                                                                 :or {approximation-factor 4 theta-const 2}}]
  (let [number-of-hashes (or number-of-hashes (* theta-const (mfn/pow cnt (/ 1 approximation-factor))))
        hash-length (or hash-length (/ number-of-hashes theta-const))
        check-buckets (fn [hash-buckets]
                        (reduce (fn [rem-elements mp]
                                  (let [bit-vectors-with-atleast-one-collision (keep (fn [[_ v]] (if (> (count v) 1) v)) mp)]
                                    (reduce #(reduce disj %1 %2) rem-elements bit-vectors-with-atleast-one-collision)))
                                (set (range cnt)) (vals hash-buckets)))
        check-for-continuity (fn [hash-buckets])
        hash-funcs (repeatedly number-of-hashes #(hash-calculating-func hash-length cnt))
        calc-hashes-fn (fn [hash-buckets [id bv]]
                         (reduce (fn [cur-hash-buckets [hash-func-id hash-func]] (update-in cur-hash-buckets [hash-func-id (hash-func bv)] #(conj % id)))
                                 hash-buckets (map-indexed vector hash-funcs)))
        bv-hash-buckets (reduce calc-hashes-fn {} bit-vectors)]
    (merge bv-stuff {:bv-hash-buckets bv-hash-buckets :hash-funcs (map-indexed vector hash-funcs)})))

(defn read-bit-vectors [fname]
  (let [d (time (with-open [rdr (clojure.java.io/reader fname)]
                  (->> (line-seq rdr) (map-indexed #(vector %1 (boolean-array (map {\0 false \1 true} %2)))) (into {}))))
        n (count d) dist-memory (atom {})]
    {:distance-memory dist-memory :bit-vectors d :count n}))

(defn read-bit-vector-solution [fname]
  (time (with-open [rdr (clojure.java.io/reader fname)]
          (->> (line-seq rdr) (filter seq)
               (map-indexed #(vector %1 (read-string %2)))
               (into (sorted-map))))))

(defn solution-quality [bv-stuff genealogy]
  (->> (tr/genealogy-to-rooted-acyclic-graph genealogy)
       :acyclic-graph
       (optimize-root-id bv-stuff)))

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

(defn solve [& {:keys [fname solution-fname sample-solution]
                :or {fname "/home/github/bitvector/data/bitvectors-genes.data.small"}}]
  (let [solution-fname (if solution-fname solution-fname (str fname ".my-parents"))
        bv (prf/prof :read (read-bit-vectors fname))
        bv-stuff (prf/prof :calc-hashes (calc-hashes-and-hash-fns bv :approximation-factor 4))
        genealogy (prf/prof :find-good-tree (find-good-tree bv-stuff))]
    (if sample-solution
      (let [sample-solution-quality (prf/prof :sample-solution-quality (solution-quality bv-stuff (read-bit-vector-solution sample-solution)))]
        (display sample-solution-quality)))
    (write-genealogy genealogy solution-fname)))

#_(prf/profile (time (solve :fname "/home/github/bitvector/data/bitvectors-genes.data.small"
                            :sample-solution "/home/github/bitvector/data/bitvectors-parents.data.small.txt")))

(defn solve-random
  ([out-fname] (let [bv-stuff (-> (generate-input-problem 10) (calc-hashes-and-hash-fns :approximation-factor 4))]
                 (write-genealogy (find-good-tree bv-stuff) out-fname)))
  ([] (solve "parents.out")))
