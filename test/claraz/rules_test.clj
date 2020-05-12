(ns claraz.rules-test
  (:require [claraz.rules :as zr]
            [clara.rules.accumulators :as acc]
            [clojure.pprint :refer [pprint]]
            [clara.rules.accumulators :as acc])
  (:require [clara.rules :as cr])
  (:use clojure.test))

(defrecord Player [id x])
(defrecord Item [id x])
(defrecord Truth [])

(zr/defquery get-truth
  []
  [?t Truth])

(zr/defquery pi-query
  [?x]
  [?p Player (= x ?x)]
  [?i Item (= x ?x)])

(deftest query-pos-args-and-keyword
  (let [r (-> (cr/mk-session
               [pi-query])
            (cr/insert (->Player 1 2))
            (cr/insert (->Player 1 2))
            (cr/insert (->Item 1 2))
            (cr/insert (->Item 1 2))
            cr/fire-rules
            (zr/query+ :pi-query 2))]
    (is (= 4 (count r)))
    (is (= 1 (-> r first :?p :id)))
    (is (= 1 (-> r first :?i :id)))
    (is (= 2 (-> r first :?x)))))

(deftest query-normal
  (let [r (-> (cr/mk-session
               [pi-query])
            (cr/insert (->Player 1 2))
            (cr/insert (->Player 1 2))
            (cr/insert (->Item 1 2))
            (cr/insert (->Item 1 2))
            cr/fire-rules
            (zr/query+ pi-query :?x 2))]
    (is (= 4 (count r)))
    (is (= 1 (-> r first :?p :id)))
    (is (= 1 (-> r first :?i :id)))
    (is (= 2 (-> r first :?x)))))

(deftest query-with-acc
  (-> (cr/mk-session
       [(zr/query q
          []
          [?p [(acc/all) Player]])])
    (cr/insert (->Player 1 2))
    (cr/insert (->Player 1 2))
    cr/fire-rules
    (zr/query+ :q)
    first :?p count (= 2) is))

(deftest rule-with-expressions
  (-> (cr/mk-session
       [get-truth
        (zr/rule r
          [?p Player]
          [:not [:or
                 [:and
                  [Player (= x 3)]
                  [Player (= x 2)]]
                 [:exists [Item]]
                 [:test (= 1 2)]]]
          =>
          (cr/insert! (->Truth)))])
    (cr/insert (->Player 1 2))
    (cr/insert (->Player 1 2))
    cr/fire-rules
    (zr/query+ get-truth)
    first is))

(deftest rule-using-let-bindings
  (-> (cr/mk-session
       [(zr/query get-item
          []
          [?i Item])
        (zr/rule r
          [?p Player [{:keys [id x] :as p}] (= x 2)]
          =>
          (cr/insert! (->Item id p)))])
    (cr/insert (->Player 1 2))
    cr/fire-rules
    (zr/query+ :get-item)
    first :?i :id (= 1) is))

(deftest implicit-acc-all
  (-> (cr/mk-session
       [(zr/query get-players
          []
          [?p [Player]])])
    (cr/insert (->Player 1 2))
    (cr/insert (->Player 2 2))
    (cr/insert (->Player 3 2))
    cr/fire-rules
    (zr/query+ :get-players)
    first :?p count (= 3) is))

(deftest query-with-extraction
  (let [r (-> (cr/mk-session
       [(zr/query q
          []
          [?p Player [{:keys [id x]}] (= x ?x)]
          [?i Item]
          =>
          [?p ?i ?x])])
    (cr/insert (->Player 1 1))
    (cr/insert (->Player 1 1))
    (cr/insert (->Item 2 2))
    (cr/insert (->Item 2 2))
    cr/fire-rules
    (zr/query+ :q))]
    (is (= 4 (count r)))
    (is (= 3 (count (first r))))
    (is (= 1 (-> r ffirst :id)))
    (is (= 2 (-> r first second :id)))))
