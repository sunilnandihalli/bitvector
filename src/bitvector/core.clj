(ns bitvector.core
  (:require [clojure.java.io :as io]
            [clojure.contrib.combinatorics :as comb]
            [clojure.data.finger-tree :as ft]
            [clojure.contrib.generic.math-functions :as mfn])
  (:import [java.io BufferedReader BufferedWriter FileReader])
  (:use iterate bitvector.debug))

(defn permutations-repeated
  ([items n]
     (if (= n 1) (map list (keys items))
         (let [func-perm-pairs (map (fn [x] [(partial cons x) (if (> (items x) 1) (update-in items [x] dec) (dissoc items x))]) (keys items))
               permutations-per-pair (let [n-1 (dec n)] (fn [[f rest-of-items]] (map f (permutations-repeated rest-of-items n-1))))]
           (mapcat permutations-per-pair func-perm-pairs))))
  ([items] (permutations-repeated items (apply + (vals items)))))

(defn center-of-tree [tree]
  {:pre [#_(do (println tree) true)]}
  (let [leaves (keep #(if (= 1 (count (second %))) (update-in % [1] seq)) tree)
        new-tree (reduce (fn [mp [lid [vid]]] (-> (dissoc mp lid) (update-in [vid] #(disj % lid)))) tree leaves)]
    (if (<= (count new-tree) 2) new-tree (recur new-tree))))

(defn children-trees [tree root]
  (if-let [children (seq (tree root))]
    (thrush-with-sym [x] (dissoc tree root)
      (reduce (fn [tr cid] (update-in tr [cid] #(disj % root))) x children)
      (map vector (repeat x) children))))

(defn cannonical-value-of-tree-rooted-at [tree root]
  (if-let [child-trees (children-trees tree root)]
    (set (map #(apply cannonical-value-of-tree-rooted-at %) child-trees)) #{}))

(defn tree-isomorphic? [free-tr1 free-tr2]
  (let [[c1 c2] (map center-of-tree [free-tr1 free-tr2])]
    (case (map count [c1 c2])
          [1 1] (apply = (map (fn [tr c] (cannonical-value-of-tree-rooted-at tr (ffirst c))) [free-tr1 free-tr2] [c1 c2]))
          [2 2] (let [[r1 r1-d] (keys c1) [r2 r2-d] (keys c2)
                      [can1 can2] (map cannonical-value-of-tree-rooted-at [free-tr1 free-tr2] [r1 r2])]
                  (or (= can1 can2) (= (cannonical-value-of-tree-rooted-at free-tr1 r1-d) can2))) false)))

(defn log-fact-d [n] (if (= n 0) 0 (+ (mfn/log n) (log-fact-d (dec n)))))
(def log-fact-d (memoize log-fact-d))
(defn log-number-of-ways-to-build-tree [cannonical-tree-rep]
  (let [n (count cannonical-tree-rep)]
    (if (= n 0) 0 (apply + (log-fact-d n) (map log-number-of-ways-to-build-tree cannonical-tree-rep)))))
(def log-number-of-ways-to-build-tree (memoize log-number-of-ways-to-build-tree))
(let [alpha 2.955765 beta 0.5349485 ln-alpha (mfn/log alpha) ln-beta (mfn/log beta)
      coefficients [0.5349496061 0.441699018 0.485387731 2.379745574]]
  (defn log-number-of-non-isomorphic-trees [n]
    (+ (* ln-alpha n) (* -2.5 (mfn/log n)) (mfn/log (apply + (map * coefficients (iterate #(/ % n) 1)))))))
(def log-number-of-non-isomorphic-trees (memoize log-number-of-non-isomorphic-trees))

(defn map-of-cannonical-values-with-all-nodes-as-roots [free-tree]
  (let [can-vals-with-sub-tree-memory (fn [[mem can-vals] id]
                                        (let [sub-tree-can-val (fn sub-tree-can-val [[p-id c-id :as k] cur-mem]
                                                                 (if-let [[_ v] (find cur-mem k)] [cur-mem v]
                                                                         (let [c-c-ids (disj (free-tree c-id) p-id)
                                                                               [new-cur-mem vs] (reduce (fn [[nc-mem vs] c-c-id]
                                                                                                          (let [[nnc-mem v] (sub-tree-can-val [c-id c-c-id] nc-mem)]
                                                                                                            [nnc-mem (conj vs v)])) [cur-mem []] c-c-ids)
                                                                               cannonical (frequencies vs)]
                                                                           [(assoc new-cur-mem [p-id c-id] cannonical) cannonical])))]
                                          (if (contains? can-vals id) [mem can-vals]
                                              (let [[new-mem v] (reduce (fn [[nmem vs] cid]
                                                                          (let [[nnmem v] (sub-tree-can-val [id cid] nmem)]
                                                                            [nnmem (conj vs v)])) [mem []] (disj (free-tree id) id))]
                                                [new-mem (assoc can-vals id (frequencies v))]))))
        [_ can-vals] (reduce can-vals-with-sub-tree-memory [{} {}] (keys free-tree))]
    can-vals))
        
#_(def d (time (let [pruf-code (random-tree 10000)
                     g (prufer-code-to-graph-rep pruf-code)
                     can-vals (map-of-cannonical-values-with-all-nodes-as-roots g)]
                 [pruf-code g can-vals])))
    


#_(def d (let [pruf-code (random-tree 10)
               g (prufer-code-to-graph-rep pruf-code)
               freq-pruf-code (frequencies pruf-code)
               perms (permutations-repeated freq-pruf-code)
               graphs (map prufer-code-to-graph-rep perms)]
           (cannonical-value-of-tree-rooted-at g 3)
           #_(map #(tree-isomorphic? g %) graphs)))
           
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
  ([f prufer-code] (for-each-edge #(f %2) nil prufer-code)))

(defn graph-to-prufer-code [graph]
  (let [leaf-nodes (into (sorted-map) (filter #(= 1 (count (second %))) graph))]
    (loop [cur-leaf-nodes leaf-nodes cur-prufer-code [] cur-graph graph]
      (if (= 2 (count cur-graph)) cur-prufer-code
          (let [[id1 neighbouring-nodes] (first cur-leaf-nodes)
                [id2] (seq neighbouring-nodes)
                rest-of-leaf-nodes (dissoc cur-leaf-nodes id1)
                new-graph (-> (dissoc cur-graph id1) (update-in [id2] #(disj % id1)))
                new-prufer-code (conj cur-prufer-code id2)
                new-leaf-nodes (into rest-of-leaf-nodes (let [l (find new-graph id2)] (if (= 1 (count (second l))) [l])))]
            (recur new-leaf-nodes new-prufer-code new-graph))))))

#_(repeatedly 1000 #(let [n (+ 2 (rand-int 1000))
                          g1 (random-tree n)
                          trf (random-node-map n)
                          trf-inv (invert-node-map trf)
                          x (map trf-inv trf)
                          g2 (thrush-with-sym [x] g1
                               (prufer-code-to-graph-rep x)
                               (transform-graph x trf)
                               (graph-to-prufer-code x)
                               (map trf-inv x))]
                      (apply = (map frequencies [g1 g2]))))

(defn number-of-tree-isomorphic-to-the-tree-represented-by-prufer-code [pruf-code])
(defn invert-node-map [node-map-vec]
  (let [n (count node-map-vec)] (reduce (fn [mp i] (assoc mp (node-map-vec i) i)) (vec (repeat n 0))  (range n))))
(defn random-tree [n] (repeatedly (- n 2) #(rand-int n)))
(defn random-node-map [n] (shuffle (range n)))
(defn add-edge-to-tree [tree [id1 id2]] (merge-with into {id1 #{id2} id2 #{id1}} tree))
(defn transform-graph [tree trf] (into {} (map (fn [[k vs]] [(trf k) (into #{} (map trf vs))]) tree)))
(defn prufer-code-to-graph-rep [pruf-code] (for-each-edge add-edge-to-tree  {} pruf-code))
                                        
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
           
    
        
        
                   
        
  
