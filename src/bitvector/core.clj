(ns bitvector.core
  (:use iterate))

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
       (loop [[first-degree-1-nodes & rest-of-degree-1-nodes :as degree-1-nodes] (keep-indexed #(when (= %2 1) %1) degree)
              cur-degree degree [cur-code & rest-of-prufer-code] prufer-code cur-f-arg f-arg]
         (if-not cur-code (f cur-f-arg degree-1-nodes)
                 (let [nf-arg (f cur-f-arg [cur-code first-degree-1-nodes])
                       new-degree (-> cur-degree (a-update [first-degree-1-nodes] dec) (a-update [cur-code] dec))]
                   (recur (if (= (aget new-degree cur-code) 1) (conj rest-of-degree-1-nodes cur-code) rest-of-degree-1-nodes)
                          new-degree rest-of-prufer-code nf-arg))))))
  ([f prufer-code] (for-each-edge (fn [_ ed] (f ed)) nil prufer-code)))

(defn read-bit-vectors [fname]
  

           
    
        
        
                   
        
  
