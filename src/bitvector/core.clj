(ns bitvector.core
  (:require [clojure.java.io :as io]
            [clojure.contrib.combinatorics :as comb]
            [clojure.data.finger-tree :as ft]
            [clojure.contrib.generic.math-functions :as mfn])
  (:import [java.io BufferedReader BufferedWriter FileReader])
  (:use iterate bitvector.debug))

(defrecord tree-node [bit-vector number-of-nodes-in-tree-rooted-here tree-quality parent-id children])
(defn log-fact [n] (if (= n 0) 0 (+ (mfn/log n) (log-fact (dec n)))))
(def log-fact (memoize log-fact))
(defn log-number-of-ways-to-build-tree [cannonical-tree-rep]
  "doubtfull .. check this later"
  (let [frqs (vals cannonical-tree-rep)
        n (apply + frqs)]
    (if (= n 0) 0 (apply + (log-fact n) #_(- (apply + (map log-fact frqs)))
                         (map (fn [[key frq]] (* frq (log-number-of-ways-to-build-tree key))) cannonical-tree-rep)))))
(def log-number-of-ways-to-build-tree (memoize log-number-of-ways-to-build-tree))
(let [alpha 2.955765 beta 0.5349485 ln-alpha (mfn/log alpha) ln-beta (mfn/log beta)
      coefficients [0.5349496061 0.441699018 0.485387731 2.379745574]]
  (defn log-number-of-non-isomorphic-trees [n]
    (+ (* ln-alpha n) (* -2.5 (mfn/log n)) (mfn/log (apply + (map * coefficients (iterate #(/ % n) 1)))))))
(def log-number-of-non-isomorphic-trees (memoize log-number-of-non-isomorphic-trees))
(defn random-highly-probable-tree [n]
  (reduce (fn [mp i] (-> mp (update-in [(rand-int i)] #(conj % i)) (assoc i nil))) {0 nil} (range 1 n)))
(defn number-of-nodes
  ([mp root-id] (apply + 1 (map (partial number-of-nodes mp) (mp root-id))))
  ([mp] (number-of-nodes mp 0)))         

(defn log-probability-and-number-of-children-of-tree
  ([mp root-id] (if-let [child-tree-root-ids (mp root-id)]
                  (let [log-prob-and-n-child-pairs (map (partial log-probability-and-number-of-children-of-tree mp) child-tree-root-ids)
                        children-tree-n-nodes (map second log-prob-and-n-child-pairs)
                        log-probs (map first log-prob-and-n-child-pairs)
                        total-children (apply + children-tree-n-nodes)
                        total-number-of-nodes-in-current-tree (inc total-children)
                        log-probability-of-current-tree (apply + (log-fact total-children) (- (apply + (map log-fact children-tree-n-nodes))) log-probs)]
                    [log-probability-of-current-tree total-number-of-nodes-in-current-tree]) [0 1]))
  ([mp] (log-probability-and-number-of-children-of-tree mp 0)))

(defn log-normal-distribution-functioin [n p]
  (let [mu (* n p) var (* mu (- 1 p))
        log-k (* (- 0.5) (+ (mfn/log 2) (mfn/log 3.141592654) (mfn/log var)))
        var-sqr (* var var)]
    (fn [x] (let [x-mu (- x mu)] (- log-k (/ (* x-mu x-mu) var-sqr))))))
           
(def mutation-probability 0.2)
(def log-p (mfn/log mutation-probability))
(def log-1-p (mfn/log (- 1 mutation-probability)))
    
(defn read-bit-vectors [fname]
  (let [d (with-open [rdr (clojure.java.io/reader fname)]
            (->> (line-seq rdr) (map-indexed #(vector %1 (boolean-array (map {\0 false \1 true} %2)))) (into {})))
        n (count d) dist-memory (atom (transient {}))]
    {:distance-memory dist-memory :bit-vectors d :count n}))

(defn bit-dist [a b]
  (loop [[fa & ra] a [fb & rb] b d 0]
    (if (not (nil? fa)) (recur ra rb (if (not= fa fb) (inc d) d)) d)))

#_(defn clone [{:keys [node-map root-id]}]
    (let [n (count node-map)
          nodes-whose-parents-need-to-be-permuted (take 2 (distinct (repeatedly #(rand-int n))))
          {p :parent-id children :children q :tree-quality n :number-of-nodes-in-tree-rooted-here bv :bit-vector :as  sub-tree} (node-map node-id)]
      (thrush-with-sym [child] parent
        (update-in child [n1 :parent-id])))) 
    
        

(defn log-bit-vector-distance-probability [{memory :distance-memory bit-vectors :bit-vectors} [i j]]
  (let [get-dist (fn [i j] (if-let [[_ v] (find @memory [i j])] v
                             (let [v (bit-dist (aget bit-vectors i) (aget bit-vectors j))]
                                 (swap! memory #(assoc! % [i j] v)) v)))]                   
    (cond (= i j) 0 (> i j) (get-dist i j) :else (get-dist j i))))

(defn calc-all-distance-probabilities [{memory :distance-memory bit-vectors :bit-vectors n :count :as w}]
  (dorun (map (partial log-bit-vector-distance-probability w)
              (for [i (range n) j (range n) :when (< i j)] [i j]))))

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

(defn average [& vs] (let [n (count vs)] (if (= n 0) 0 (/ (apply + vs) n))))

(defn log-sum [& logs]
  (let [m (apply average logs)]
    (thrush-with-sym [x] (map #(- % m) logs) (map mfn/exp x) (apply + x) (mfn/log x) (+ m x))))
(defn log-mult [& logs] (apply + logs))
(defn log-div [& logs] (apply - logs))
(defn log-pow [base power] (* power base))
(defn log-combinations [n r] (log-div (log-fact n) (log-fact r) (log-fact (- n r))))
(defn log-permutations [n r] (log-div (log-fact n) (log-fact r)))
(defn log-probability [n bit-dist n-seperation-links]
  (let [log-modified-p (apply log-sum (map
                                   (fn [i] (log-mult (log-combinations n-seperation-links i)
                                                     (log-pow log-p i)
                                                     (log-pow log-1-p (- n-seperation-links i))))
                                   (filter even? (range (inc n-seperation-links)))))
        log-1-modified-p (mfn/log (- 1 (mfn/exp log-modified-p)))]
    (log-mult (log-pow log-modified-p bit-dist) (log-pow log-1-modified-p (- n bit-dist)))))

(defn hash-calculating-func [hash-length]
  (let [ids (take hash-length (shuffle (range 10000)))]
    (fn [bv] (reduce (fn [hash [hash-loc-id bv-pos-id]]
                       (if (aget bv bv-pos-id)
                           (bit-set hash hash-loc-id) hash)) 0 (map-indexed vector ids)))))

(defn calc-hashes-and-hash-fns [{:keys [bit-vectors count] :as bv-stuff}]
  (let [hash-length 20 number-of-hashes 20
        hash-funcs (repeatedly number-of-hashes #(hash-calculating-func 20))
        calc-hashes-fn (fn [hash-buckets [id bv]]
                         (reduce (fn [cur-hash-buckets hash-func] (update-in cur-hash-buckets (hash-func bv) #(conj % id)))
                                 hash-buckets hash-funcs))
        bv-hash-buckets (reduce calc-hashes-fn {} bit-vectors)]
    (assoc bv-stuff :bv-hash-buckets bv-hash-buckets)))

#_(map #(log-probability 100 90 %) (range 1 100 2))
#_(let [a (range 1 10)
        logs-a (map mfn/log a)]
    (mfn/exp (apply log-sum logs-a)))
    
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
