(ns bitvector.test.core
  (:use [bitvector.core])
  (:use [clojure.test]))

(deftest test-read-bit-vectors
  (is (read-bit-vectors "/home/github/bitvector/data/bitvectors-genes.data.small")))
