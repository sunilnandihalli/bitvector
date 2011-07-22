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

(defn add-edge-to-graph [transient-mst [start end]]
  (-> transient-mst
      (non-std-update! start #(if % (conj! % end) (transient #{end})))
      (non-std-update! end #(if % (conj! % start) (transient #{start})))))

(defn update-disjoint-transient-mst-coll [disjoint-transient-mst-coll transient-nodes-to-mst-id-map [s e :as edge]]
  (let [tree-ids (keep transient-nodes-to-mst-id-map edge)
        [tr1 tr2] (map disjoint-transient-mst-coll tree-ids)
        new-transient-tree (thrush-with-sym [x] (count tree-ids)
                             (case x 0 (transient {}) 1 tr1 2 (non-std-into! tr1 tr2))
                             (add-edge-to-graph x [s e]))
        new-tree-id (if-not (seq tree-ids) (inc (ffirst (rseq disjoint-transient-mst-coll))) (first tree-ids))
        new-disjoint-transient-mst-coll (thrush-with-sym [x] disjoint-transient-mst-coll
                                          (reduce dissoc x tree-ids) (assoc x new-tree-id new-transient-tree))
        new-transient-nodes-to-mst-id-map (reduce #(non-std-update! %1 %2 (constantly new-tree-id)) transient-nodes-to-mst-id-map 
     (reduce #(non-std-update! %1 (fn [s] (disj! s %2))) nodes-not-in-any-mst [s e])]))
    
(defn mst-prim-edges [edges f disjoint-transient-mst-coll transient-nodes-to-mst-id-map]
  ;; mst is also used to check as to which nodes are already present in the current estimate of the MST
  (let [all-potential-edges (thrush-with-sym [x] edges
                              (filter #(apply not= (map transient-nodes-to-mst-id-map %)) x)
                              (map (fn [[& cur-edge]] [(f cur-edge) (list cur-edge)]) x)
                              (merge-with (sorted-map) into x))]
    (loop [cur-disjoint-transient-mst-coll disjoint-transient-mst-coll
           [[cur-dist cur-dist-edge-set :as cur-dist-edge-set-pair] & rest-of-dist-edge-set-pairs :as all-dist-edge-set-pairs] (seq all-potential-edges)
           [cur-dist-edge & rest-of-cur-dist-edges] nil
           cur-transient-nodes-to-mst-id-map transient-nodes-to-mst-id-map]
      (cond
       cur-dist-edge (let [[new-disjoint-transient-mst-coll new-transient-nodes-to-mst-id-map]
                           (update-disjoint-transient-mst-set cur-disjoint-transient-mst-coll cur-transient-nodes-to-mst-id-map cur-dist-edge)]
                       (recur new-disjoint-transient-mst-coll all-dist-edge-set-pairs rest-of-cur-dist-edges new-transient-nodes-to-mst-id-map))
       cur-dist-edge-set-pair (recur cur-disjoint-transient-mst-coll rest-of-dist-edge-set-pairs (seq cur-dist-edge-set) cur-transient-nodes-to-mst-id-map)
       :else [cur-disjoint-transient-mst-coll cur-transient-nodes-to-mst-id-map]))))
      
(defn mst-prim-with-priority-edges [{cnt :count :as bv-stuff} probable-edge-map]
  (let [pb-edg-map (ensure-sortedness probable-edge-map)]
    (loop [[[_ cur-equal-priority-edge-set] & remaining-priority-edge-set-pairs] pb-edg-map
           cur-disjoint-transient-mst-coll (list)
           cur-nods-not-in-mst (transient (set (range cnt)))]
      
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
  (let [graph-rep (prf/prof :probable-graph (probable-graph bv-stuff))
        is-graph-connected (prf/prof :is-graph-connected (tr/is-graph-connected graph-rep))
        minimum-spanning-free-tree (prf/prof :mst-prim (tr/mst-prim graph-rep (fnd [x] (bit-dist bv-stuff x))))
        {:keys [log-num-ways log-parent-child-probability total-quality opt-root-id] :as new-sol-quality}
        (prf/prof :optimize-root-id (optimize-root-id bv-stuff minimum-spanning-free-tree))
        genealogy (prf/prof :rooted-acyclic-graph-to-genealogy (tr/rooted-acyclic-graph-to-genealogy [minimum-spanning-free-tree opt-root-id]))] genealogy))
           
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