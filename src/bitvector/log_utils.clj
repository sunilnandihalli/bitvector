(ns bitvector.log-utils
  (:require [clojure.contrib.generic.math-functions :as mfn])
  (:use iterate bitvector.debug clojure.inspector))


(defn log-fact [n] (if (= n 0) 0 (+ (mfn/log n) (log-fact (dec n)))))
(def log-fact (memoize log-fact))
(defn average [& vs] (let [n (count vs)] (if (= n 0) 0 (/ (apply + vs) n))))

(defn log-sum [& logs]
  (let [m (apply average logs)]
    (thrush-with-sym [x] (map #(- % m) logs) (map mfn/exp x) (apply + x) (mfn/log x) (+ m x))))
(defn log-mult [& logs] (apply + logs))
(defn log-div [& logs] (apply - logs))
(defn log-pow [base power] (* power base))
(defn log-combinations [n r] (log-div (log-fact n) (log-fact r) (log-fact (- n r))))
(defn log-permutations [n r] (log-div (log-fact n) (log-fact r)))

(defn log-normal-distribution-functioin [n p]
  (let [mu (* n p) var (* mu (- 1 p))
        log-k (* (- 0.5) (+ (mfn/log 2) (mfn/log 3.141592654) (mfn/log var)))
        var-sqr (* var var)]
    (fn [x] (let [x-mu (- x mu)] (- log-k (/ (* x-mu x-mu) var-sqr))))))

  