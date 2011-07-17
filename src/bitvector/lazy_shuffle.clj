(ns bitvector.lazy-shuffle)
(defn create-shuffle-object [lst]
  (map #(ref %) lst))

(defn swap-elements [el1 el2]
  (let [tmp @el1]
    (dosync (ref-set el1 @el2)
            (ref-set el2 tmp))))

(defn lazy-shuffle-core [s-lst len]
  (lazy-seq
   (if (= 1 len)
     s-lst
     (let [fst-el (first s-lst)
           rst (rest s-lst)
           nlen (dec len)
           swap-el (nth rst (int (rand nlen)))]
       (swap-elements fst-el swap-el)
       (cons fst-el (lazy-shuffle-core rst nlen))))))

(defn fetch-elements [s-lst]
  (map (fn [el] @el) s-lst))

(defn lazy-shuffle [lst fetch-len]
  (let [len (count lst)
        s-lst (create-shuffle-object lst)]
    (if (> fetch-len len)
         (fetch-elements (take len (lazy-shuffle-core s-lst len)))
         (fetch-elements (take fetch-len (lazy-shuffle-core s-lst len))))))
  