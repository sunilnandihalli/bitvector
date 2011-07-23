(ns bitvector.core
  (:require [clojure.java.io :as io]
            [clojure.contrib.combinatorics :as comb]
            [clojure.data.finger-tree :as ft]
            [clojure.contrib.generic.math-functions :as mfn]
            [clojure.contrib.profile :as prf]
            [bitvector.tree-utils :as tr])            
  (:import [java.io BufferedReader BufferedWriter FileReader])
  (:use iterate bitvector.debug clojure.inspector bitvector.log-utils))

(def mutation-probability 0.2)
(def log-p (mfn/log mutation-probability))
(def log-1-p (mfn/log (- 1 mutation-probability)))
(def log-1-p-over-p (- log-1-p log-p))

(defrecord tree-node [bit-vector number-of-nodes-in-tree-rooted-here tree-quality parent-id children])
(defn abs [x] (if (< x 0) (- x) x))

(defn-memoized log-parent-child-probability [bit-cnt dist]
  (log-mult (log-pow log-p dist) (log-pow log-1-p (- bit-cnt dist))))
           
(defn hash-calculating-func [hash-length dimension-d]
  (let [ids (take hash-length (shuffle (range dimension-d)))]
    (fn [bv] (reduce (fn [hash [hash-loc-id bv-pos-id]]
                       (if (aget bv bv-pos-id)
                         (bit-set hash hash-loc-id) hash)) 0 (map-indexed vector ids)))))

(defn number-of-collisions-per-node [{:keys [bv-hash-buckets]}]
  (let [update-freq (fn [mp [_ coll]]
                      (let [n-1 (dec (count coll))]
                        (reduce (fn [cur-mp node-id] (update-in cur-mp [[:node node-id]] #(if % (+ % n-1) n-1))) mp coll)))
        update-for-a-given-hash-func (fn [mp [_ hash-func-map]] (reduce update-freq mp hash-func-map))
        collisions-map (reduce update-for-a-given-hash-func {} bv-hash-buckets)
        collision-frequencies (into (sorted-map) (frequencies (vals collisions-map)))]
    collision-frequencies))

(defn probable-nearest-bv-ids [{:keys [bv-hash-buckets hash-funcs bit-vectors] :as bv-stuff} id]
  (thrush-with-sym [x] hash-funcs (mapcat (fn [[hf-id hf]] ((bv-hash-buckets hf-id) (hf (bit-vectors id)))) x)
    (distinct x) (filter #(not= % id) x)))

(defn all-probable-edges [{:keys [bv-hash-buckets] :as bv-stuff}]
  (let [inc-or-init #(if % (inc %) 1)]
    (loop [[[_ cur-hash-buckets] & rest-of-hash-buckets :as all-remaining-hash-buckets] bv-hash-buckets
           [[_ cur-bucket-nodes] & rest-of-hash-buckets-of-nodes :as w] nil
           pb-edges (transient {})]
      (cond
       cur-bucket-nodes (recur all-remaining-hash-buckets rest-of-hash-buckets-of-nodes
                               (loop [[e & rest-of-es] (comb/combinations cur-bucket-nodes 2) pb-edges pb-edges]
                                 (if-not e pb-edges
                                         (recur rest-of-es (non-std-update! pb-edges (set e) inc-or-init)))))
       cur-hash-buckets (recur rest-of-hash-buckets nil pb-edges)
       :else (persistent! pb-edges)))))
                        
(defn bit-dist [{memory :distance-memory bit-vectors :bit-vectors} [i j]]
  (prf/prof :bit-dist (let [bit-dist-help (fn [a b]
                                            (loop [[fa & ra] a [fb & rb] b d 0]
                                              (if (not (nil? fa)) (recur ra rb (if (not= fa fb) (inc d) d)) d)))
                            get-dist (fn [i j] (if-let [[_ v] (find @memory [i j])] v
                                                       (let [v (bit-dist-help (bit-vectors i) (bit-vectors j))]
                                                         (swap! memory #(assoc % [i j] v)) v)))]                   
                        (cond (= i j) 0 (> i j) (get-dist i j) :else (get-dist j i)))))

(defn map-of-probable-edges [{:keys [bv-hash-buckets] :as bv-stuff}]
  (let [probable-edges (all-probable-edges bv-stuff)
        trnsnt-n-collisions-2-trnsnt-edgset-map (loop [[[edge n-hash-collisions :as edge-pair] & rest-of-edge-collision-pairs] probable-edges
                                                       n-collision-edges-map (transient {})]
                                                  (if-not edge-pair n-collision-edges-map
                                                          (recur rest-of-edge-collision-pairs
                                                                 (non-std-update! n-collision-edges-map n-hash-collisions #(if % (conj! % edge) (transient #{edge}))))))]
    (reduce (fn [persistent-sorted-map [n-hash-collisions transient-edge-set]]
              (assoc persistent-sorted-map n-hash-collisions (persistent! transient-edge-set)))
            (sorted-map) (persistent! trnsnt-n-collisions-2-trnsnt-edgset-map))))    

(defn add-edge-to-graph [mst [start end]]
  (-> mst (update-in [start] #(if % (conj % end) #{end})) (update-in [end] #(if % (conj % start) #{start}))))

(defn update-disjoint-mst-coll [[disjoint-mst-coll nodes-to-mst-id-map] [s e :as edge]]
  (let [[tr-id1 tr-id2 :as tree-ids] (keep nodes-to-mst-id-map edge)
        [tr1 tr2] (map disjoint-mst-coll tree-ids)
        n-tr-ids (count tree-ids)
        new-tree (-> (case n-tr-ids 0 {} 1 tr1 2 (into tr1 tr2)) (add-edge-to-graph [s e]))
        new-tree-id (case n-tr-ids 
                          0 (inc (ffirst (rseq disjoint-mst-coll)))
                          1 (first tree-ids)
                          2 (if (> (count tr1) (count tr2)) tr-id1 tr-id2))
        new-disjoint-mst-coll (-> (reduce dissoc disjoint-mst-coll tree-ids) (assoc new-tree-id new-tree))
        assign-new-tree-id #(assoc %1 %2 new-tree-id)
        new-nodes-to-mst-id-map (thrush-with-sym [x]
                                  (reduce assign-new-tree-id nodes-to-mst-id-map edge)
                                  (condp = new-tree-id ;; can simplify .. written this way for performance...
                                      tr-id1 (reduce assign-new-tree-id x (keys tr2))
                                      tr-id2 (reduce assign-new-tree-id x (keys tr1)) x))]
    [disjoint-mst-coll nodes-to-mst-id-map]))     
    
(defn mst-prim-edges [edges f [disjoint-mst-coll nodes-to-mst-id-map]]
  ;; mst is also used to check as to which nodes are already present in the current estimate of the MST
  (let [all-potential-edges (thrush-with-sym [x] edges
                              (filter #(let [[tr-id1 tr-id2] (map nodes-to-mst-id-map %)]
                                         (or (not (and tr-id1 tr-id2)) (not= tr-id1 tr-id2)))  x)
                              (map (fn [[& cur-edge]] [(f cur-edge) (list cur-edge)]) x)
                              (merge-with (sorted-map) into x))]
    (loop [[[cur-dist cur-dist-edge-set :as cur-dist-edge-set-pair] & rest-of-dist-edge-set-pairs :as all-dist-edge-set-pairs] (seq all-potential-edges)
           [cur-dist-edge & rest-of-cur-dist-edges] nil
           [cur-disjoint-mst-coll cur-nodes-to-mst-id-map] [disjoint-mst-coll nodes-to-mst-id-map]]
      (cond
       cur-dist-edge (recur all-dist-edge-set-pairs rest-of-cur-dist-edges (update-disjoint-mst-coll [cur-disjoint-mst-coll cur-nodes-to-mst-id-map] cur-dist-edge))
       cur-dist-edge-set-pair (recur rest-of-dist-edge-set-pairs (seq cur-dist-edge-set) [cur-disjoint-mst-coll cur-nodes-to-mst-id-map])
       :else [cur-disjoint-mst-coll cur-nodes-to-mst-id-map]))))
      
(defn mst-prim-with-priority-edges [{cnt :count :as bv-stuff} probable-edge-map]
  (let [pb-edg-map (ensure-sortedness probable-edge-map)
        edge-cost #(bit-dist bv-stuff %)]
    (loop [[[_ cur-equal-priority-edge-set] & remaining-priority-edge-set-pairs] pb-edg-map [cur-disjoint-mst-coll cur-nodes-to-mst-id-map] [{} {}]]
      (recur remaining-priority-edge-set-pairs (mst-prim-edges cur-equal-priority-edge-set edge-cost [cur-disjoint-mst-coll cur-nodes-to-mst-id-map])))))
      
(defn-memoized log-probability-of-bv [r n]
  (log-mult (log-pow log-p r) (log-pow log-1-p (- n r))))

(defn optimize-root-id [{:keys [count bit-vectors] :as bv-stuff} gr]
  (let [{:keys [opt-root-id log-num-ways]} (tr/most-probable-root-for-a-given-tree gr)
        log-parent-child-probability (reduce + (map (fn [[i j]]
                                                      (let [dist (bit-dist bv-stuff [i j])]
                                                        (log-probability-of-bv dist count))) (prf/prof :edges-in-prufer-order (tr/edges-in-prufer-order gr))))
        total-quality (log-mult log-num-ways log-parent-child-probability)]
    (self-keyed-map log-num-ways log-parent-child-probability total-quality opt-root-id))) 

(defn write-genealogy
  ([genealogy out-fname]
     (let [parents (apply str (interpose "\n" (vals (into (sorted-map) genealogy))))]
       (spit out-fname parents)))
  ([genealogy] (write-genealogy genealogy "parents.out")))

(defn find-good-tree [{cnt :count :as bv-stuff} & {:keys [n-iterations] :or {n-iterations 100}}]
  (let [probable-edges (map-of-probable-edges bv-stuff)
        minimum-spanning-free-tree (mst-prim-with-priority-edges probable-edges)
        {:keys [log-num-ways log-parent-child-probability total-quality opt-root-id] :as new-sol-quality} (optimize-root-id bv-stuff minimum-spanning-free-tree)
        genealogy (tr/rooted-acyclic-graph-to-genealogy [minimum-spanning-free-tree opt-root-id])] genealogy))
           
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
               (into {})))))
                    
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

(defn solve
  ([fname out-fname]
     (let [bv (prf/prof :read (read-bit-vectors fname))
           bv-stuff (prf/prof :calc-hashes (calc-hashes-and-hash-fns bv :approximation-factor 4))
           genealogy (prf/prof :find-good-tree (find-good-tree bv-stuff))]
       (write-genealogy  genealogy out-fname)))
  ([out-fname] (let [bv-stuff (-> (generate-input-problem 10) (calc-hashes-and-hash-fns :approximation-factor 4))]
                 (write-genealogy (find-good-tree bv-stuff) out-fname)))
  ([] (solve "parents.out")))


(defn hello2 [& is]
  (apply + is))

(defn hello1 []
  (prf/prof :hello (apply hello2 (range 1000))))

#_(prf/profile (hello1))