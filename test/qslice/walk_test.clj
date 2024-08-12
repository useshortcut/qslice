(ns qslice.walk-test
  (:require
   [clojure.test :refer [deftest is testing]]
   [qslice.walk :as walk])
  (:import
   (clojure.lang
    ArraySeq)))

(deftest map-aseq-test
  (let [v [0 1 2 3 4 5]
        cnt (count v)
        xs (sort v)
        xs-next (next xs)
        xs-rest (rest xs)]

    (testing "ArraySeq assumptions"
      ;; These are semi-internal interfaces and assumptions of how ArraySeqs work
      ;; that map-aseq relies on.
      ;; These tests are here to catch if future Clojure versions change them!
      (is (instance? ArraySeq xs))
      (is (instance? ArraySeq xs-next))
      (is (instance? ArraySeq xs-rest))

      (is (== 0 (.index ^ArraySeq xs)))
      (is (== 1 (.index ^ArraySeq xs-next)))
      (is (== 1 (.index ^ArraySeq xs-rest)))

      (is (== cnt (alength (.array ^ArraySeq xs))))
      (is (identical? (.array ^ArraySeq xs) (.array ^ArraySeq xs-next)))
      (is (identical? (.array ^ArraySeq xs) (.array ^ArraySeq xs-rest))))

    (testing "map-aseq with base ArraySeq"
      (let [xs' (walk/map-aseq inc xs)]
        (is (instance? ArraySeq xs'))
        (is (= xs (seq v)) "map-aseq should not mutate original array")
        (is (= xs' (seq [1 2 3 4 5 6])))
        (is (zero? (.index xs')))))

    (testing "map-aseq with rest ArraySeq"
      (let [xs' (walk/map-aseq inc xs-rest)]
        (is (instance? ArraySeq xs'))
        (is (= xs (seq v)) "map-aseq should not mutate original array")
        (is (= xs' (seq [2 3 4 5 6])))
        (is (== (dec cnt) (alength (.array xs'))))
        (is (zero? (.index xs')) "map-aseq should not hold head of original array items")))

    (testing "map-aseq with next ArraySeq"
      (let [xs' (walk/map-aseq inc xs-next)]
        (is (instance? ArraySeq xs'))
        (is (= xs (seq v)) "map-aseq should not mutate original array")
        (is (= xs' (seq [2 3 4 5 6])))
        (is (== (dec cnt) (alength (.array xs'))))
        (is (zero? (.index xs')) "map-aseq should not hold head of original array items")))))
