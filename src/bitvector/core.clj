(ns bitvector.core
  (:require [clojure.java.io :as io])
  (:import [java.io BufferedReader BufferedWriter FileReader])
  (:use iterate))

(def mutation-probability 0.2)

(defn a-update [arr [:as keys] f]
  (let [v (f (apply aget arr keys))]
    (apply aset arr (conj keys v)) arr))
#_(let [tree-ex [3 9 4 5 1 6 7 8 2 0]
        pruf-code [2 8 9 7 6 1 5 4]]
    (for-each-edge println pruf-code))

#_(let [pruf-code [6 3 3 0 6 0]]
    (for-each-edge println pruf-code))

#_(let [tree-ex [0 2 3 1]
        pruf-code [2 3]]
    (for-each-edge println pruf-code))

#_(let [tree-ex [0 2 1]
        pruf-code [2]]
    (for-each-edge println pruf-code))

(defn for-each-edge
  ([f f-arg prufer-code]
     "calls f with f-arg as the first argument ,initially and return value of previous call to
      f subsequently, and every edge being passed as a pair of nodes"
     (let [n (+ (count prufer-code) 2)
           degree (loop [deg (int-array n 1) [cur-code & rest-of-prufer-code] prufer-code]
                    (if-not cur-code deg (recur (a-update deg [cur-code] inc) rest-of-prufer-code)))]
       (loop [degree-1-nodes (into (sorted-set) (keep-indexed #(when (= %2 1) %1) degree))
              cur-degree degree [cur-code & rest-of-prufer-code] prufer-code cur-f-arg f-arg]
         (if-not cur-code (f cur-f-arg (vec degree-1-nodes))
                 (let [first-degree-1-node (first degree-1-nodes)
                       nf-arg (f cur-f-arg [cur-code first-degree-1-node])
                       new-degree (-> cur-degree (a-update [first-degree-1-node] dec) (a-update [cur-code] dec))
                       rest-of-degree-1-nodes (disj degree-1-nodes first-degree-1-node)]
                   (recur (if (= (aget new-degree cur-code) 1) (conj rest-of-degree-1-nodes cur-code) rest-of-degree-1-nodes)
                          new-degree rest-of-prufer-code nf-arg))))))
  ([f prufer-code] (for-each-edge (fn [_ ed] (f ed)) nil prufer-code)))

(defn graph-to-prufer-code [graph]
  (let [leaf-nodes (into (sorted-map) (filter #(= 1 (count (graph (second %)))) graph))]
    (loop [cur-leaf-nodes leaf-nodes cur-prufer-code [] cur-graph graph]
      (if (= 2 (count cur-graph)) cur-prufer-code
          (let [[id1 neighbouring-nodes] (first cur-leaf-nodes)
                [id2] (seq neighbouring-nodes)
                rest-of-leaf-nodes (disj cur-leaf-nodes id1)
                new-graph (-> (disj cur-graph id1) (update-in id2 #(disj % id1)))
                new-prufer-code (conj cur-prufer-code id2)
                new-leaf-nodes (into rest-of-leaf-nodes (let [l (find new-graph id2)] (if (= 1 (count (second l))) l)))]
            (recur new-leaf-nodes new-prufer-code new-graph))))))
        
            
      
(defn random-tree [n] (repeatedly (- n 2) #(rand-int n)))
(defn random-node-map [n] (shuffle (range n)))
(defn add-edge-to-tree [tree [id1 id2]] (merge-with into {id1 #{id2} id2 #{id1}} tree))
(defn transform-graph [tree trf] (into {} (map (fn [[k vs]] [(trf k) (into #{} (map trf vs))]) tree)))
                                        
(defn check-isomorphism [pruf-code node-map]
  (let [graph1 (for-each-edge add-edge-to-tree {} pruf-code)
        graph2 (for-each-edge add-edge-to-tree {} (map node-map pruf-code))
        graph1-transformed (transform-graph graph1 node-map)]
    (clojure.pprint/pprint [graph1 graph2 graph1-transformed])
    (= graph2 graph1-transformed)))

#_(let [n 10 rand-tree (random-tree n) rand-node-map (random-node-map n)]
    (println ['n n])
    (println ['rand-tree rand-tree])
    (println ['rand-node-map rand-node-map])
    (check-isomorphism rand-tree rand-node-map))
    

(defn read-bit-vectors [fname]
  (let [d (with-open [rdr (clojure.java.io/reader fname)]
            (->> (line-seq rdr) (map #(boolean-array (map {\0 false \1 true} %))) into-array))
        n (count d) dist-memory (into-array (map #(short-array % (short -1)) (range n)))]
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

(defn distance [{memory :distance-memory bit-vectors :bit-vectors} [i j]]
  (let [get-dist (fn [i j] (let [d (aget memory i j)]
                             (if (= d -1)
                               (let [nd (bit-dist (aget bit-vectors i) (aget bit-vectors j))]
                                 (aset memory i j (short nd)) nd) d)))]                   
    (cond (= i j) 0 (> i j) (get-dist i j) :else (get-dist j i))))

(defn most-probable-root-node-given-a-tree [prufer-code])
  

(defn display-bit-vectors [{:keys [bit-vectors]}]
  (dorun (map-indexed #(println (str %1 " : " (apply str (map {true 1 false 0} %2)))) bit-vectors)))
#_(def d (read-bit-vectors "/home/github/bitvector/data/bitvectors-genes.data.small"))
#_(def d (generate-random-bit-vector-set 1000))                
#_(def d (generate-input-problem 100))
#_(display-bit-vectors d)
           
    
        
        
                   
        
  
