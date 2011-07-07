(ns bitvector.core
  (:require [clojure.java.io :as io]
            [clojure.contrib.combinatorics :as comb]
            [clojure.data.finger-tree :as ft]
            [clojure.contrib.generic.math-functions :as mfn])
  (:import [java.io BufferedReader BufferedWriter FileReader])
  (:use iterate bitvector.debug))


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

(defn log-probability-of-current-permutation-of-bitvectors-for-current-tree [mp bit-vectors])

(defn log-normal-distribution-functioin [n p]
  (let [mu (* n p) var (* mu (- 1 p))
        log-k (* (- 0.5) (apply + (mfn/log 2) (mfn/log 3.141592654) (mfn/log var)))
        var-sqr (* var var)]
    (fn [x] (let [x-mu (- x mu)] (- log-k (/ (* x-mu x-mu) var-sqr))))))
           
(def mutation-probability 0.2)
    
(defn read-bit-vectors [fname]
  (let [d (with-open [rdr (clojure.java.io/reader fname)]
            (->> (line-seq rdr) (map #(boolean-array (map {\0 false \1 true} %))) into-array))
        n (count d) dist-memory {}]
    {:distance-memory dist-memory :bit-vectors d :count n}))

(defn generate-random-bit-vector-set [n]
  (let [d (->> (fn [] (boolean-array (repeatedly n #({0 false 1 true} (rand-int 2))))) (repeatedly n)  into-array)
        dist-memory (into-array (map #(short-array % (short -1)) (range n)))]
    {:distance-memory dist-memory :bit-vectors d :count n}))

(defn generate-input-problem [n]
  (let [clone (fn [parent mut-prob] (boolean-array (map #(if (< (rand) mut-prob) (not %) %) parent)))
        bit-vectors (into-array (reduce (fn [population _] (conj population (clone (rand-nth population) mutation-probability)))
                                        [(boolean-array (repeatedly n #({0 false 1 true} (rand-int 2))))] (range (dec n))))
        dist-memory (into-array (map #(short-array % (short -1)) (range n)))]
    {:distance-memory dist-memory :bit-vectors bit-vectors :count n}))

(defn bit-dist [a b]
  {:pre [(do (dorun (map #(println (apply str (map {true 1 false 0} %))) [a b]))  true)]} 
  (loop [[fa & ra] a [fb & rb] b d 0]
    (if (not (nil? fa)) (recur ra rb (if (not= fa fb) (inc d) d)) d)))

(defn log-bit-vector-distance-probability [{memory :distance-memory bit-vectors :bit-vectors} [i j]]
  (let [get-dist (fn [i j] (let [d (aget memory i j)]
                             (if (= d -1)
                               (let [nd (bit-dist (aget bit-vectors i) (aget bit-vectors j))]
                                 (aset memory i j (short nd)) nd) d)))]                   
    (cond (= i j) 0 (> i j) (get-dist i j) :else (get-dist j i))))

(defn display-bit-vectors [{:keys [bit-vectors]}]
  (dorun (map-indexed #(println (str %1 " : " (apply str (map {true 1 false 0} %2)))) bit-vectors)))
#_(def d (read-bit-vectors "/home/github/bitvector/data/bitvectors-genes.data.small"))
#_(def d (generate-random-bit-vector-set 1000))                
#_(def d (generate-input-problem 100))
#_(display-bit-vectors d)
           
    
        
        
                   
        
  
