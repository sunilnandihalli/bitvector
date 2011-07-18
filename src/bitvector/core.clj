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

(defrecord tree-node [bit-vector number-of-nodes-in-tree-rooted-here tree-quality parent-id children])
(defn abs [x] (if (< x 0) (- x) x))
(defn-memoized log-parent-child-probability [bit-cnt dist]
  (log-mult (log-pow log-p dist) (log-pow log-1-p (- bit-cnt dist))))

(defn log-hierarchy-seperation-probability [n bit-dist n-seperation-links]
  (let [log-modified-p (apply log-sum (map
                                   (fn [i] (log-mult (log-combinations n-seperation-links i)
                                                     (log-pow log-p i)
                                                     (log-pow log-1-p (- n-seperation-links i))))
                                   (filter even? (range (inc n-seperation-links)))))
        log-1-modified-p (mfn/log (- 1 (mfn/exp log-modified-p)))]
    (log-mult (log-pow log-modified-p bit-dist) (log-pow log-1-modified-p (- n bit-dist)))))
           
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

(defn probable-links-to [{:keys [bv-hash-buckets hash-funcs] :as bv-stuff} id]
  (map vector (repeat id) (probable-nearest-bv-ids bv-stuff id)))

(defn generate-random-probable-solution [{:keys [bit-vectors bv-hash-buckets hash-funcs] cnt :count :as bv-stuff}]
  (let [root-id (rand-int cnt)
        len-comp (fn [x y] (< (bit-dist bv-stuff x) (bit-dist bv-stuff y)))
        initial-probable-link-pairs (map (fn [x y] [[x y] (/ 1.0 (abs (log-parent-child-probability cnt (bit-dist bv-stuff [x y]))))])
                                         (repeat root-id) (probable-nearest-bv-ids bv-stuff root-id))]
    (loop [parent-nodes #{root-id} available-nodes (disj (set (range cnt)) root-id)
           probable-link-pairs initial-probable-link-pairs cur-genealogy {root-id -1}]
      (if (empty? available-nodes) cur-genealogy
          (let [cumulative-probs (into (sorted-map) (reductions (fn [[sum _] [lnk p]] [(+ sum p) lnk]) 0 probable-link-pairs))
                max-prob (ffirst (rseq cumulative-probs))
                [parent-node new-node] (second (ffirst (subseq cumulative-probs > (rand max-prob))))
                new-available-nodes (disj new-node available-nodes)
                new-parent-nodes (conj new-node parent-nodes)
                new-probable-links (concat (filter (fn [[[_ cid] _]] (not= cid new-node)) probable-link-pairs)
                                           (map (fn [x y] [[x y] (/ 1.0 (bit-dist bv-stuff [x y]))])
                                                (repeat new-node) (filter (comp not new-parent-nodes) (probable-nearest-bv-ids bv-stuff new-node))))
                new-genealogy (assoc cur-genealogy new-node parent-node)]
            (recur  new-parent-nodes new-available-nodes new-probable-links new-genealogy))))))

(defn optimize-root-id [gr rt-id] [(tr/log-probability-and-number-of-children-of-tree graph-rep optimized-root-id) rt-id])

(defn find-good-tree [bv-stuff & {:keys [n-iterations] :or [n-iterations 100]}]
  (loop [i 0 cur-best-sol nil cur-quality nil]
    (if (= i n-iterations) cur-best-sol
        (let [rand-sol (generate-random-probable-solution bv-stuff)
              [graph-rep root-id] (genealogy-to-rooted-tree rand-sol)
              [new-sol-quality optimized-root-id] (optimize-root-id graph-rep root-id)
              [new-best-sol new-quality] (if-not cur-best-sol [[graph-rep optimize-root-id] new-sol-quality]
                                           (if (> new-sol-quality cur-quality) [[graph-rep optimize-root-id] new-sol-quality]
                                               [cur-best-sol cur-quality]))]
          (recur (inc i) new-best-sol new-quality)))))              
  

#_(def d (number-of-collisions-per-node big-data))
#_(def e (let [small-data (thrush-with-sym [x]
                            (read-bit-vectors "/home/github/bitvector/data/bitvectors-genes.data.small")
                            (calc-hashes-and-hash-fns x :approximation-factor 2))]
           (number-of-collisions-per-node small-data)))
            
(defn bit-dist [{memory :distance-memory bit-vectors :bit-vectors} [i j]]
  (let [bit-dist-help (fn [a b]
                        (loop [[fa & ra] a [fb & rb] b d 0]
                          (if (not (nil? fa)) (recur ra rb (if (not= fa fb) (inc d) d)) d)))
        get-dist (fn [i j] (if-let [[_ v] (find @memory [i j])] v
                                   (let [v (bit-dist-help (bit-vectors i) (bit-vectors j))]
                                     (swap! memory #(assoc % [i j] v)) v)))]                   
    (cond (= i j) 0 (> i j) (get-dist i j) :else (get-dist j i))))

(defn-memoized log-probability-of-bv [r n]
  (log-mult (log-pow log-p r) (log-pow log-1-p (- n r))))

(defn closest-point [{:keys [bit-vectors bv-hash-buckets hash-funcs] cnt :count :as bv-stuff} query-bv-id
                     & {:keys [closest-point-among]}]
  (let [closest-point-among (or closest-point-among #(not= query-bv-id %))
        cur-bv (bit-vectors query-bv-id)
        probable-nearest-bv-ids (thrush-with-sym [x] hash-funcs
                                  (mapcat (fn [[hf-id hf]] ((bv-hash-buckets hf-id) (hf cur-bv))) x)
                                  (filter closest-point-among x) (distinct x))]
    (apply min-key #(bit-dist bv-stuff [query-bv-id %]) probable-nearest-bv-ids)))

(defn brute-force-closest [{:keys [bit-vectors] cnt :count :as bv-stuff} query-bv-id]
  (apply (juxt min-key max-key) #(bit-dist bv-stuff [query-bv-id %]) (filter #(not= % query-bv-id) (range cnt))))
        
(defn calc-hashes-and-hash-fns [{:keys [bit-vectors] cnt :count :as bv-stuff} & {:keys [approximation-factor theta-const hash-length number-of-hashes]
                                                                                 :or {approximation-factor 4 theta-const 2}}]
  (let [number-of-hashes (or number-of-hashes (* theta-const (mfn/pow cnt (/ 1 approximation-factor))))
        hash-length (or hash-length (/ number-of-hashes theta-const))
        check-buckets (fn [hash-buckets]
                        (reduce (fn [rem-elements mp]
                                  (let [bit-vectors-with-atleast-one-collision (keep (fn [[_ v]] (if (> (count v) 1) v)) mp)]
                                    (reduce #(reduce disj %1 %2) rem-elements bit-vectors-with-atleast-one-collision)))
                                (set (range cnt)) (vals hash-buckets)))
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

(defn display-bit-vectors [{:keys [bit-vectors]}]
  (dorun (map-indexed #(println (str %1 " : " (apply str (map {true 1 false 0} %2)))) bit-vectors)))

(defn generate-random-bit-vector-set [n]
  (let [d (->> (fn [] (boolean-array (repeatedly n #({0 false 1 true} (rand-int 2))))) (repeatedly n)  into-array)
        dist-memory {}]
    {:distance-memory dist-memory :bit-vectors d :count n}))

(defn generate-input-problem [n]
  (let [clone (fn [parent mut-prob] (boolean-array (map #(if (< (rand) mut-prob) (not %) %) parent)))
        bit-vectors (into-array (reduce (fn [population _] (conj population (clone (rand-nth population) mutation-probability)))
                                        [(boolean-array (repeatedly n #({0 false 1 true} (rand-int 2))))] (range (dec n))))
        dist-memory {}]
    {:distance-memory dist-memory :bit-vectors bit-vectors :count n}))

#_(map #(log-probability 100 90 %) (range 1 100 2))
#_(let [a (range 1 10)
        logs-a (map mfn/log a)]
    (mfn/exp (apply log-sum logs-a)))
#_(def big-data (read-bit-vectors "/home/github/bitvector/data/bigdata"))
#_(def small-data (read-bit-vectors "/home/github/bitvector/data/bitvectors-genes.data.small"))
#_(let [d (time (read-bit-vectors "/home/github/bitvector/data/bigdata"))
        d1 (time (calc-all-distance-probabilities d))])
#_(def d (read-bit-vectors "/home/github/bitvector/data/bitvectors-genes.data.small"))
#_(def d (read-bit-vectors "/home/github/bitvector/data/bigdata"))
#_(def d (generate-random-bit-vector-set 1000))                
#_(def d (generate-input-problem 100))
#_(display-bit-vectors d)
#_(let [vc (vec (repeatedly 10000 #(rand-int 10000)))
        mp (into {} (map-indexed vector vc))]
    (map #(time (dotimes [i 100000] (% (rand-int 10000)))) [vc mp]))
