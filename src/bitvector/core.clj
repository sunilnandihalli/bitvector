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
      
(defn optimize-root-id [{:keys [count bit-vectors] :as bv-stuff} {:keys [acyclic-graph]}]
  "optimize root id such that the permutations of the clonings needed to create the given tree is maximized"
  (let [{:keys [opt-root-id log-num-ways all-root-log-num-ways]} (tr/most-probable-root-for-a-given-tree acyclic-graph)
        total-parent-child-dist (reduce (fn [s edge] (+ s (bit-dist bv-stuff edge))) 0 (prf/prof :edges-in-prufer-order (tr/edges-in-prufer-order acyclic-graph)))
        log-parent-child-probability (log-mult (log-pow log-p total-parent-child-dist) (log-pow log-1-p (- (* count count) total-parent-child-dist)))
        total-quality (log-mult log-num-ways log-parent-child-probability)]
    (self-keyed-map log-num-ways log-parent-child-probability all-root-log-num-ways total-quality opt-root-id))) 

(defn write-genealogy
  "output the genealogy in the specified format"
  ([genealogy out-fname]
     (let [parents (apply str (interpose "\n" (vals (into (sorted-map) genealogy))))]
       (spit out-fname parents)))
  ([genealogy] (write-genealogy genealogy "parents.out")))

(defn move-root-in-genealogy [genealogy new-root-id]
  (loop [cur-genealogy genealogy to-be-updated new-root-id prev -1]
    (if (= to-be-updated -1) cur-genealogy
        (recur (assoc cur-genealogy to-be-updated prev) (cur-genealogy to-be-updated) to-be-updated))))

(defn add-edge-to-tree-ensuring-resulting-tree-is-better-than-original [{:keys [genealogy tried-edges prioritized-edges total-distance n-disjoint-trees] :as bv-stuff}]
  {:pre [tried-edges genealogy]}
  (let [[[& [s e :as new-edge] :as new-edge-as-set]] (peek prioritized-edges)
        [s-parent e-parent :as se] (map genealogy new-edge)
        dist (partial bit-dist bv-stuff)
        new-edge-dist (bit-dist bv-stuff new-edge)]
    (-> (cond 
         (and s-parent e-parent) (let [[path-between-end-points-of-new-edge is-disjoint] (loop [cur-s s s-path [s]]
                                                                                           (let [cur-parent-s (genealogy cur-s)]
                                                                                             (condp = cur-parent-s
                                                                                                 -1 (loop [cur-e e e-path [e]]
                                                                                                      (let [cur-parent-e (genealogy cur-e)]
                                                                                                        (condp = cur-parent-e
                                                                                                            -1 (let [[trimmed-s-path trimmed-e-path]
                                                                                                                     (loop [n-s-path s-path n-e-path e-path]
                                                                                                                       (let [p-s (peek n-s-path)
                                                                                                                             p-e (peek n-e-path)]
                                                                                                                         (if (not= p-s p-e)
                                                                                                                           [(conj n-s-path (genealogy p-s))
                                                                                                                            (conj n-e-path (genealogy p-e))]
                                                                                                                           (recur (pop n-s-path) (pop n-e-path)))))] 
                                                                                                                 [[trimmed-s-path trimmed-e-path] (not (= cur-e cur-s))])
                                                                                                            s [[nil (conj e-path s)] false] 
                                                                                                            (recur cur-parent-e (conj e-path cur-parent-e)))))
                                                                                                 e [[(conj s-path e) nil] false]
                                                                                                 (recur cur-parent-s (conj s-path cur-parent-s)))))]
                                   (if is-disjoint (assoc bv-stuff :genealogy (-> (move-root-in-genealogy genealogy s) (assoc s e))
                                                          :total-distance (+ total-distance new-edge-dist) :n-disjoint-trees (dec n-disjoint-trees)) 
                                       (let [[start-list end-list :as path-edge-list] (map #(partition 2 1 %) path-between-end-points-of-new-edge)
                                             [[d-edg-s _ :as max-edge] max-dist new-edge-end-id] (apply max-key second
                                                                                                        (mapcat #(map (fn [edg] [edg (dist edg) %2]) %1)
                                                                                                                path-edge-list (range)))]
                                         (if-not (< new-edge-dist max-dist) bv-stuff
                                                 (assoc bv-stuff 
                                                   :genealogy (thrush-with-sym [x] (assoc genealogy d-edg-s -1)
                                                                (move-root-in-genealogy x (nth new-edge new-edge-end-id))
                                                                (assoc x (nth new-edge new-edge-end-id) (nth new-edge (case new-edge-end-id 1 0 0 1))))
                                                   :total-distance (- (+ total-distance new-edge-dist) max-dist))))))
         s-parent (-> (assoc-in bv-stuff [:genealogy e] s) (assoc :total-distance (+ new-edge-dist total-distance)))
         e-parent (-> (assoc-in bv-stuff [:genealogy s] e) (assoc :total-distance (+ new-edge-dist total-distance)))
         :else (-> (assoc-in bv-stuff [:genealogy s] e)
                   (assoc-in [:genealogy e] -1)
                   (assoc :total-distance (+ new-edge-dist total-distance) :n-disjoint-trees (inc n-disjoint-trees))))
        (assoc :tried-edges (conj tried-edges new-edge-as-set) :prioritized-edges (pop prioritized-edges)))))

(defn add-an-extra-hash-func [{:keys [bit-vectors hash-length number-of-hashes prioritized-edges tried-edges]
                               :or {prioritized-edges (pm/priority-map-by >) number-of-hashes 0 tried-edges #{}} cnt :count :as bv-stuff}]
  (let [new-hash-func (hash-calculating-func hash-length cnt)
        hash-buckets (persistent! (reduce (fn [cur-hash-buckets [id bv]] (non-std-update! cur-hash-buckets (new-hash-func bv) #(conj % id))) (transient {}) bit-vectors))
        new-prioritized-edges (reduce (fn [cur-prioritized-edges [hash-val bvs-with-same-hash]]
                                        (reduce (fn [cur-cur-prioritized-edges e]
                                                  (let [se (set e)]
                                                    (if-not (tried-edges se)
                                                      (update-in cur-cur-prioritized-edges [se] inc-or-init) cur-cur-prioritized-edges)))
                                                cur-prioritized-edges (comb/combinations bvs-with-same-hash 2))) prioritized-edges hash-buckets)]
    (assoc! bv-stuff :prioritized-edges new-prioritized-edges :number-of-hashes (inc number-of-hashes))))

(defn add-n-extra-hash-funcs [bv-stuff n]
  (persistent! (reduce (fn [cur-bv-stuff _] (add-an-extra-hash-func cur-bv-stuff)) (transient bv-stuff) (range n))))
                       
(defn find-good-tree [{:keys [delta-number-of-hashes error-percentage] cnt :count :or {delta-number-of-hashes 5 error-percentage 0.1} :as bv-stuff}]
  (let [{:keys [genealogy] :as bv-stuff}
        (loop [{:keys [total-distance prioritized-edges] :as cur-bv-stuff} bv-stuff]
          (let [{new-dist :total-distance :keys [genealogy n-disjoint-trees tried-edges number-of-hashes] :as new-bv-stuff}
                (reduce
                 (fn [{:keys [tried-edges n-disjoint-trees number-of-hashes total-distance genealogy n-disjoint-trees] :as cc-bv-stuff} i]
                   (let [n-tried-edges (count tried-edges)
                         genealogy-size (count genealogy)]
                     (if (zero? (mod n-tried-edges cnt))
                       (println (self-keyed-map n-tried-edges n-disjoint-trees number-of-hashes total-distance genealogy-size n-disjoint-trees))))
                   (add-edge-to-tree-ensuring-resulting-tree-is-better-than-original cc-bv-stuff))
                 cur-bv-stuff (range (count prioritized-edges)))
                [new-genealogy-size number-of-edges-tried] [(count genealogy) (count tried-edges)]]
            (if (and (= n-disjoint-trees 1) (= new-genealogy-size cnt) (< (abs (- total-distance new-dist)) (* error-percentage cnt))) new-bv-stuff
                (recur (add-n-extra-hash-funcs new-bv-stuff delta-number-of-hashes)))))
        {:keys [acyclic-graph] :as minimum-spanning-free-tree} (tr/genealogy-to-rooted-acyclic-graph genealogy)
        {:keys [opt-root-id] :as sol-quality}  (optimize-root-id bv-stuff minimum-spanning-free-tree)
        genealogy (tr/rooted-acyclic-graph-to-genealogy {:acyclic-graph acyclic-graph :root-id opt-root-id})]
    (self-keyed-map sol-quality genealogy)))

(defn calc-hashes-and-hash-fns [{:keys [bit-vectors] cnt :count :as bv-stuff} & {:keys [approximation-factor theta-const hash-length number-of-hashes]
                                                                                 :or {approximation-factor 4 theta-const 2}}]
  "calculate the hash functions and store the bit-vector ids in the corresponding buckets"
  (let [number-of-hashes (or number-of-hashes (* theta-const (mfn/pow cnt (/ 1 approximation-factor))))
        hash-length (or hash-length (/ number-of-hashes theta-const))]
    (add-n-extra-hash-funcs (assoc bv-stuff :hash-length hash-length :genealogy {} :total-distance 0 :n-disjoint-trees 0 :tried-edges #{}) number-of-hashes)))

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

(defn solution-quality [bv-stuff genealogy]
  "estimate the quality of given genealogy with respect to the bitvectors from bv-stuff"
  (->> (tr/genealogy-to-rooted-acyclic-graph genealogy)
       (optimize-root-id bv-stuff)))

(defn solve [& {:keys [fname solution-fname sample-solution n-increments delta-n-hashes]
                :or {fname "/home/github/bitvector/data/bitvectors-genes.data.small"}}]
  (let [solution-fname (if solution-fname solution-fname (str fname ".my-parents"))
        bv (prf/prof :read (read-bit-vectors fname))
        sample-solution-quality (if sample-solution (display (prf/prof :sample-solution-quality (solution-quality bv (read-bit-vector-solution sample-solution)))))
        bv-stuff (prf/prof :calc-hashes (calc-hashes-and-hash-fns bv :approximation-factor 4))
        {:keys [sol-quality genealogy] :as sol} (find-good-tree bv-stuff)]
    (display sol)
    (write-genealogy genealogy solution-fname)))
    
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
  ([] (solve-random "parents.out")))
