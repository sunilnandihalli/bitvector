(ns bitvector.core
  (:require [clojure.java.io :as io]
            [clojure.contrib.combinatorics :as comb]
            [clojure.data.finger-tree :as ft]
            [clojure.contrib.generic.math-functions :as mfn]
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
  (mapcat #(comb/combinations % 2) (mapcat vals (vals bv-hash-buckets))))

(defn probable-links-to [{:keys [bv-hash-buckets hash-funcs] :as bv-stuff} id]
  (map vector (repeat id) (probable-nearest-bv-ids bv-stuff id)))

(defn bit-dist [{memory :distance-memory bit-vectors :bit-vectors} [i j]]
  (let [bit-dist-help (fn [a b]
                        (loop [[fa & ra] a [fb & rb] b d 0]
                          (if (not (nil? fa)) (recur ra rb (if (not= fa fb) (inc d) d)) d)))
        get-dist (fn [i j] (if-let [[_ v] (find @memory [i j])] v
                                   (let [v (bit-dist-help (bit-vectors i) (bit-vectors j))]
                                     (swap! memory #(assoc % [i j] v)) v)))]                   
    (cond (= i j) 0 (> i j) (get-dist i j) :else (get-dist j i))))


(defn closest-point [{:keys [bit-vectors bv-hash-buckets hash-funcs] cnt :count :as bv-stuff} query-bv-id
                     & {:keys [closest-point-among]}]
  (let [closest-point-among (or closest-point-among #(not= query-bv-id %))
        cur-bv (bit-vectors query-bv-id)
        probable-nearest-bv-ids (thrush-with-sym [x] hash-funcs
                                  (mapcat (fn [[hf-id hf]] ((bv-hash-buckets hf-id) (hf cur-bv))) x)
                                  (filter closest-point-among x) (distinct x))]
    (apply min-key #(bit-dist bv-stuff [query-bv-id %]) probable-nearest-bv-ids)))

(defn split-nodes-at-bit [{:keys [bit-vectors] :as bv-stuff} s bit-n] (vals (group-by (fn [[_ bv]] [bit-n (aget bv bit-n)]) s)))
(defn split-edges-at-bit [bit-id s1 s2 edge-coll] (group-by (fn [[i j]] (cond (every? s1 [i j]) [bit-id 1] (every? s2 [i j]) [bit-id 2] :else [bit-id 1 2])) edge-coll))
(defn min-edge [bv-stuff edge-coll] (if (seq edge-coll) (apply min-key #(bit-dist bv-stuff %) edge-coll)))


(defn probable-graph [{:keys [bv-hash-buckets] :as bv-stuff}]
  (-> bv-stuff all-probable-edges tr/edges-to-graph))
                  
(defn-memoized log-probability-of-bv [r n]
  (log-mult (log-pow log-p r) (log-pow log-1-p (- n r))))

(defn optimize-root-id [{:keys [count bit-vectors] :as bv-stuff} gr]
  (let [{:keys [opt-root-id log-num-ways]} (tr/most-probable-root-for-a-given-tree gr)
        log-parent-child-probability (reduce + (map (fn [[i j]]
                                                      (let [dist (bit-dist bv-stuff [i j])]
                                                        (log-probability-of-bv dist count))) (tr/edges-in-prufer-order gr)))
        total-quality (log-mult log-num-ways log-parent-child-probability)]
    (self-keyed-map log-num-ways log-parent-child-probability total-quality opt-root-id))) 

(defn write-genealogy
  ([genealogy out-fname]
     (let [parents (apply str (interpose "\n" (vals (into (sorted-map) genealogy))))]
       (spit out-fname parents)))
  ([genealogy] (write-genealogy genealogy "parents.out")))

(defn find-good-tree [{cnt :count :as bv-stuff} & {:keys [n-iterations] :or {n-iterations 100}}]
  (let [graph-rep (probable-graph bv-stuff)
        minimum-spanning-free-tree (tr/mst-prim graph-rep (fnd [x] (bit-dist bv-stuff x)))
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

(defn-memoized read-bit-vectors [fname]
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
     (let [bv-stuff (-> (read-bit-vectors fname)
                        (calc-hashes-and-hash-fns :approximation-factor 4))]
       (write-genealogy (find-good-tree bv-stuff) out-fname)))
  ([out-fname] (let [bv-stuff (-> (generate-input-problem 10) (calc-hashes-and-hash-fns :approximation-factor 4))]
                 (write-genealogy (find-good-tree bv-stuff) out-fname)))
  ([] (solve "parents.out")))
