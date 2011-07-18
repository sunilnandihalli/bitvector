(ns bitvector.tree-utils
  (:require [clojure.contrib.generic.math-functions :as mfn])
  (:use iterate bitvector.debug clojure.inspector bitvector.log-utils))

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

(defn cannonical-value-of-tree-rooted-at [[mem tree root]]
  (if-let [child-trees (children-trees tree root)]
    (set (map #(apply cannonical-value-of-tree-rooted-at %) child-trees)) #{}))

(defn tree-isomorphic? [free-tr1 free-tr2]
  (let [[c1 c2] (map center-of-tree [free-tr1 free-tr2])]
    (case (map count [c1 c2])
          [1 1] (apply = (map (fn [tr c] (cannonical-value-of-tree-rooted-at tr (ffirst c))) [free-tr1 free-tr2] [c1 c2]))
          [2 2] (let [[r1 r1-d] (keys c1) [r2 r2-d] (keys c2)
                      [can1 can2] (map cannonical-value-of-tree-rooted-at [free-tr1 free-tr2] [r1 r2])]
                  (or (= can1 can2) (= (cannonical-value-of-tree-rooted-at free-tr1 r1-d) can2))) false)))
(defn sub-tree-cannonical-value [free-tree]
  (let [inc-or-init #(or (and % (inc %)) 1)]
    (fn sub-tree-can-val [[p-id c-id :as k] cur-mem]
      (if-let [[_ v] (find cur-mem k)] [cur-mem v]
              (let [c-c-ids (disj (free-tree c-id) p-id)
                    [new-cur-mem cannonical] (reduce (fn [[nc-mem vs] c-c-id]
                                                       (let [[nnc-mem v] (sub-tree-can-val [c-id c-c-id] nc-mem)]
                                                         [nnc-mem (update-in vs [v] inc-or-init)]))
                                                     [cur-mem {}] c-c-ids)]
                [(assoc new-cur-mem [p-id c-id] cannonical) cannonical])))))

(defn cannonical-values-with-sub-tree-memory [free-tree]
  (let [inc-or-init #(or (and % (inc %)) 1)
        sub-tree-can-val (sub-tree-cannonical-value free-tree)]
    (fn [[mem can-vals] id]
      (if (contains? can-vals id) [mem can-vals]
          (let [[new-mem v] (reduce (fn [[nmem vs] cid]
                                      (let [[nnmem v] (sub-tree-can-val [id cid] nmem)]
                                        [nnmem (update-in vs [v] inc-or-init)])) [mem {}] (free-tree id))]
            [new-mem (assoc can-vals id v)])))))

(defn map-of-cannonical-values-with-all-nodes-as-roots [free-tree]
  (let [[_ can-vals] (reduce (cannonical-values-with-sub-tree-memory free-tree) [{} {}] (keys free-tree))]
    can-vals))    

(defn-memoized log-number-of-ways-to-build-tree [cannonical-tree-rep]
  "doubtfull .. check this later"
  (let [frqs (vals cannonical-tree-rep)
        n (apply + frqs)]
    (if (= n 0) 0 (apply + (log-fact n) #_(- (apply + (map log-fact frqs)))
                         (map (fn [[key frq]] (* frq (log-number-of-ways-to-build-tree key))) cannonical-tree-rep)))))

(let [alpha 2.955765 beta 0.5349485 ln-alpha (mfn/log alpha) ln-beta (mfn/log beta)
      coefficients [0.5349496061 0.441699018 0.485387731 2.379745574]]
  (defn-memoized log-number-of-non-isomorphic-trees [n]
    (+ (* ln-alpha n) (* -2.5 (mfn/log n)) (mfn/log (apply + (map * coefficients (iterate #(/ % n) 1)))))))

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

(defn generate-random-genealogy [n]
  (let [root-id (rand-int n)]
    (loop [genealogy {root-id -1} available-parents [root-id]
           [f-av-n & rest-of-av-nodes] (seq (disj (set (range n)) root-id))]
      (if-not f-av-n genealogy
              (recur (assoc genealogy f-av-n (rand-nth available-parents))
                     (conj available-parents f-av-n) rest-of-av-nodes)))))
#_(generate-random-genealogy 40)

(defn genealogy-to-rooted-tree [genealogy]
  (reduce (fn [[graph root-id] [child-id parent-id]]
            (if (= parent-id -1) [graph child-id]
                [(-> graph
                     (update-in [child-id] #(if % (conj % parent-id) #{parent-id}))
                     (update-in [parent-id] #(if % (conj % child-id) #{child-id}))) root-id]))
          [{} -1] genealogy))

(defn rooted-tree-to-genealogy [[graph root-id]]
  (loop [genealogy {root-id -1} cur-graph graph [first-root & rest-of-roots] [root-id]]
    (if-not first-root genealogy
            (let [new-roots (cur-graph first-root)]
              (recur (reduce #(assoc %1 %2 first-root) genealogy new-roots)
                     (reduce (fn [gr n-root] (update-in gr [n-root] #(disj % first-root))) cur-graph new-roots)
                     (into rest-of-roots new-roots))))))

#_(let [tr (generate-random-genealogy 100)]
    (println tr)
    (= tr (-> tr genealogy-to-rooted-tree rooted-tree-to-genealogy)))        

#_(def d (time (let [pruf-code (random-tree 5)
                     g (prufer-code-to-graph-rep pruf-code)
                     can-vals (map-of-cannonical-values-with-all-nodes-as-roots g)
                     num-ways (map (fn [[root-id cannonical]] [root-id (log-number-of-ways-to-build-tree cannonical)]) can-vals)
                     c (center-of-tree g)
                     ways-root-ids-group (into {}
                                               (map (fn [[k vs]] [k (map first vs)])
                                                    (group-by second num-ways)))
                     max-ways-root-id (apply max-key first ways-root-ids-group)]
                 [max-ways-root-id ways-root-ids-group g c can-vals])))
#_(def d (let [pruf-code (random-tree 10)]
           (prufer-code-to-graph-rep pruf-code)))
               

#_(def d (let [pruf-code (random-tree 10)
               g (prufer-code-to-graph-rep pruf-code)
               freq-pruf-code (frequencies pruf-code)
               perms (permutations-repeated freq-pruf-code)
               graphs (map prufer-code-to-graph-rep perms)]
           (cannonical-value-of-tree-rooted-at g 3)
           #_(map #(tree-isomorphic? g %) graphs)))


(defn a-update [arr [:as keys] f]
  (let [v (f (apply aget arr keys))]
    (apply aset arr (conj keys v)) arr))


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

(defn best-roots [free-tree]
  (let [can-vals (map-of-cannonical-values-with-all-nodes-as-roots free-tree)
        num-ways (into {} (map (fn [[root-id cannonical]] [root-id (log-number-of-ways-to-build-tree cannonical)]) can-vals))
        ways-root-ids-group (reduce (fn [mp [id q]] (update-in mp [q] #(conj % id))) num-ways)
        [q max-ways-root-ids :as ret] (apply max-key first num-ways)] ret))

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

(defn permutations-repeated
  ([items n]
     (if (= n 1) (map list (keys items))
         (let [func-perm-pairs (map (fn [x] [(partial cons x) (if (> (items x) 1) (update-in items [x] dec) (dissoc items x))]) (keys items))
               permutations-per-pair (let [n-1 (dec n)] (fn [[f rest-of-items]] (map f (permutations-repeated rest-of-items n-1))))]
           (mapcat permutations-per-pair func-perm-pairs))))
  ([items] (permutations-repeated items (apply + (vals items)))))
