(ns qslice.core-test
  (:require
   [clojure.test :refer [deftest is are]]
   [qslice.core :as qslice]))

(deftest where-form-parsing
  (let [parse @#'qslice/where-form-exposed-datalog-variables]
    (are [form vars] (= (parse form) vars)

      [] []
      ;; data pattern
      '[[?a :attr ?b]] '[$ ?a ?b]
      ;; with datasource
      '[[$d ?a :attr ?b]] '[$d ?a ?b]

      ;; predicate
      '[[(mypred ?a [?c ?d])]]    '[?a]
      '[[(mypred $d ?a [?c ?d])]] '[$d ?a]
      ;; function
      '[[(myfn ?a [?c ?d]) ?out]]                 '[?a ?out]
      '[[(myfn ?a [?c ?d]) _]]                    '[?a]
      '[[(myfn ?a [?c ?d]) [?out ...]]]           '[?a ?out]
      '[[(myfn ?a [?c ?d]) [_ ...]]]              '[?a]
      '[[(myfn ?a [?c ?d]) [[?out1 _ ?out2]]]]    '[?a ?out1 ?out2]
      '[[(myfn $d ?a [?c ?d]) ?out]]              '[$d ?a ?out]
      '[[(myfn $d ?a [?c ?d]) _]]                 '[$d ?a]
      '[[(myfn $d ?a [?c ?d]) [?out ...]]]        '[$d ?a ?out]
      '[[(myfn $d ?a [?c ?d]) [_ ...]]]           '[$d ?a]
      '[[(myfn $d ?a [?c ?d]) [[?out1 _ ?out2]]]] '[$d ?a ?out1 ?out2]

      ;; rule
      '[(myrule ?a [?c ?d])]    '[$ % ?a]
      '[($d myrule ?a [?c ?d])] '[$d % ?a]

      ;; not-join
      '[(not-join [?a ?b] [?a ?b ?c] [?d ?e ?f])]    '[$ ?a ?b]
      '[($d not-join [?a ?b] [?a ?b ?c] [?d ?e ?f])] '[$d ?a ?b]
      '[(not-join [?a ?b] (and [?a ?b ?c]) (or-join [?d ?e ?f]) (not-join [?g]))]    '[$ ?a ?b]
      '[($d not-join [?a ?b] (and [?a ?b ?c]) (or-join [?d ?e ?f]) (not-join [?g]))] '[$d ?a ?b]

      ;; not
      '[(not [?a ?b ?c] [?d ?e ?f])]    '[$ ?a ?b ?c ?d ?e ?f]
      '[($d not [?a ?b ?c] [?d ?e ?f])] '[$d ?a ?b ?c ?d ?e ?f]

      ;; or-join
      '[(or-join [?a ?b] [?a ?b ?c] [?d ?e ?f])]    '[$ ?a ?b]
      '[($d or-join [?a ?b] [?a ?b ?c] [?d ?e ?f])] '[$d ?a ?b]
      '[(or-join [?a ?b] (and [?a ?b ?c]) (not [?d ?e ?f]) (or-join [?g]))]    '[$ ?a ?b]
      '[($d or-join [?a ?b] (and [?a ?b ?c]) (not [?d ?e ?f]) (or-join [?g]))] '[$d ?a ?b]

      ;; or
      '[(or [?a ?b ?c] [?d ?e ?f])]    '[$ ?a ?b ?c ?d ?e ?f]
      '[($d or [?a ?b ?c] [?d ?e ?f])] '[$d ?a ?b ?c ?d ?e ?f]

      ;; nested or, and, not
      '[(or [?a] (and [?b] [?c] [?d]))]        '[$ ?a ?b ?c ?d]
      '[(or [?a] (and [?b] (or [?c] (not [?d]))))]  '[$ ?a ?b ?c ?d]

      ;; nested datasources
      '[($a or
            [$ ?b ?c]
            ($ not [?c ?d]))]
      '[$a ?b ?c ?d]

      ;; degenerate top-level "and" interpreted as a rule
      '[(and [?a :attr ?b])] '[$ %]

      ;; degenerate datasource references within a rule
      '[($d not
            [$h _]
            [$f _]
            ($j or-join [?a] [?a]))] '[$d ?a]

      ;; subquery
      '[[(q '[:find ?x :in $ :where [?y]] $a) [[?out]]]] '[$a ?out])))


(deftest qslice-errors
  (are [expected-error form]
       (= (try form ::not-thrown
               (catch Exception e
                 (::qslice/error (ex-data e))))
          expected-error)

    :unknown-let-binding-var
    (qslice/qslice :where '[[?c]] :let '{?x 1})

    :unsatisfied-must-let
    (qslice/qslice
     :where '[[?c ?d]]
     :provide '[?c]
     :must-let '[?c]
     :let '{?d 1})

    :unsatisfied-must-let
    (-> (qslice/qslice
         :where '[[?c ?d]]
         :provide '[?c]
         :must-let '[?c])
        (qslice/with-let '?d 1))

    :unsatisfied-must-let
    (qslice/compiled-query
     [(qslice/qslice
       :where '[[?c ?d]]
       :provide '[?c]
       :must-let '[?c])]
     '[?c])

    :invalid-with-let-arg
    (-> (qslice/qslice :where '[[?c ?d]])
        (qslice/with-let '?c))

    :invalid-with-let-arg
    (-> (qslice/qslice :where '[[?c ?d]])
        (qslice/with-let '?c 1 '?d))

    :required-and-provided-var
    (qslice/qslice :require '[?a] :provide '[?a])

    :required-and-provided-var
    (qslice/qslice :require '[$ %] :provide '[$ %])


    :unlet-able-vars
    (qslice/qslice :must-let '[?a])

    :required-and-must-let-var
    (qslice/qslice :require '[?a] :must-let '[?a])

    :missing-find
    (qslice/compiled-query
     [(qslice/qslice :provide '[?a] :let '{?a 1})]
     [])

    :missing-find
    (qslice/compiled-query
     [(qslice/rule-qslice '%)
      (qslice/qslice :provide '[?a] :let '{?a 1})]
     ['%])

    :missing-find
    (qslice/compiled-query
     [(qslice/qslice :provide '[?a] :let '{?a 1})]
     {:with ['?a]})

    :unprovided-find+with-var
    (qslice/compiled-query
     [(qslice/qslice :provide '[?a] :let '{?a 1})]
     {:find ['?unprovided]})

    :unprovided-find+with-var
    (qslice/compiled-query
     [(qslice/qslice :provide '[?a] :let '{?a 1})]
     {:find ['?a] :with ['?unprovided]})

    :unprovided-special-vars
    (qslice/compiled-query
     [(qslice/qslice :where '[[?a ?b ?c]])]
     '[?a])

    :unprovided-special-vars
    (qslice/compiled-query
     [(qslice/db-qslice 'db)
      (qslice/qslice :where '[(rule-name ?a)])]
     '[?a])

    :multiply-owned-var
    (qslice/compiled-query
     [(qslice/qslice :provide '[?a ?b] :must-let '[?b] :let '{?b 1})
      (qslice/qslice :provide '[?b ?c] :must-let '[?b] :let '{?b 1})]
     '[?a])


    :unsatisfied-require-variables
    (qslice/compiled-query
     [(qslice/qslice :require '[?a])
      (qslice/qslice :provide '[?a] :let '{?a 1})]
     '[?a])

    :unsatisfied-require-variables
    (qslice/compiled-query
     [(qslice/qslice :provide '[?a] :let '{?a 1})
      (qslice/qslice :require '[?a] :selectivity -100)]
     '[?a])))

(deftest qslice-let-equivalences
  (let [argmap {:where '[[?a ?b]]
                :must-let '[?a]
                :name "foo"
                :selectivity 100}
        unbound (qslice/qslice argmap)
        bound (qslice/qslice (assoc argmap :let '[[?a 1] [?b 2]]))]
    (is (= unbound (apply qslice/qslice (sequence cat argmap))))
    (is (= bound (apply qslice/qslice :let '[[?a 1] [?b 2]] (sequence cat argmap))))
    (is (= bound (qslice/with-let unbound '?a 1 '?b 2)))
    (is (= bound (qslice/with-let unbound '{?a 1 ?b 2})))
    (is (= bound (qslice/with-let* unbound '{?a 1 ?b 2})))
    (is (= bound (qslice/with-let* unbound (list ['?a 1] ['?b 2]))))

    ;; rebinding obliterates previous :let
    (is (= (qslice/qslice (assoc argmap :let '{?a 99}))
           (qslice/with-let bound '?a 99)))
    (is (= (qslice/qslice (assoc argmap :let '{?a 99}))
           (qslice/with-let* bound {'?a 99})))))

(deftest with-selectivity
  (is (= 0 (::qslice/selectivity (qslice/qslice))))
  (is (= 10 (::qslice/selectivity (qslice/qslice :selectivity 10))))
  (is (= 10 (::qslice/selectivity (qslice/with-selectivity (qslice/qslice) 10))))
  (is (= 5 (::qslice/selectivity (-> (qslice/qslice :selectivity 10)
                                     (qslice/with-selectivity 5)))))
  (is (= 5 (::qslice/selectivity (-> (qslice/qslice)
                                     (qslice/with-selectivity 10)
                                     (qslice/with-selectivity 5))))))

(deftest with-name
  (is (= "" (qslice/name (qslice/qslice))))
  (is (= :foo (qslice/name (qslice/qslice :name :foo))))
  (is (= :foo (qslice/name (-> (qslice/qslice)
                               (qslice/with-name :foo)))))

  (is (= :bar (qslice/name (-> (qslice/qslice :name :foo)
                               (qslice/with-name :bar)))))

  (is (= :bar (qslice/name (-> (qslice/qslice)
                               (qslice/with-name :foo)
                               (qslice/with-name :bar))))))

(deftest qslice-constructed-internals
  (are [form expect] (= (select-keys form (keys expect)) expect)
    (qslice/qslice) #::qslice{:name ""
                              :selectivity 0
                              :where-forms []
                              :let-pairs []
                              :must-let-vars-checked? true}
    (qslice/qslice {:name "foo"
                    :selectivity -1})
    #::qslice{:name "foo"
              :selectivity -1}

    (qslice/qslice :where '[[?c]] :let '{?c 1})
    '#::qslice{:must-let-vars          #{},
               :require-specials       #{$},
               :where-vars             #{$ ?c},
               :where-forms            [[?c]],
               :shaded-vars            [?c],
               :letable-vars           #{?c},
               :must-let-vars-checked? true,
               :provide-variables      #{},
               :provide-specials       #{},
               :let-vars               #{?c},
               :owned-vars             #{},
               :selectivity            0,
               :let-pairs              [[?c 1]],
               :name                   "",
               :require-variables      #{}}


    ;; automatic datasource and rule requiring and must-let
    (qslice/qslice :where [])
    #::qslice{:require-specials #{}
              :must-let-vars #{}}

    (qslice/qslice :where '[[?c]])
    #::qslice{:require-specials #{'$}
              :must-let-vars #{}}

    (qslice/qslice :where '[[?c]])
    #::qslice{:require-specials #{'$}
              :must-let-vars #{}}

    (qslice/qslice :where '[(rule-name ?a ?b ?c)])
    #::qslice{:require-specials #{'$ '%}
              :must-let-vars #{}}

    (qslice/qslice :where '[(rule-name ?a ?b ?c)
                            [?c]])
    #::qslice{:require-specials #{'$ '%}
              :must-let-vars #{}}


    (qslice/qslice :where '[[$d1 ?c]])
    #::qslice{:require-specials #{'$d1}
              :must-let-vars #{}}

    (qslice/qslice :where '[($d1 rule-name ?a ?b ?c)
                            [$d2 ?c]])
    #::qslice{:require-specials #{'$d1 '$d2 '%}
              :must-let-vars #{}}

    (qslice/qslice :provide ['$])
    #::qslice{:require-specials #{}
              :provide-specials #{'$}
              :owned-vars #{'$}
              :must-let-vars #{'$}}


    (qslice/qslice :provide ['$d])
    #::qslice{:require-specials #{}
              :provide-specials #{'$d}
              :owned-vars #{'$d}
              :must-let-vars #{'$d}}


    (qslice/qslice :provide ['%])
    #::qslice{:require-specials #{}
              :provide-specials #{'%}
              :owned-vars #{'%}
              :must-let-vars #{'%}}

    (qslice/qslice :where '[[$ ?c] (rule-name ?d)]
                   :provide '[$d])
    #::qslice{:require-specials #{'$ '%}
              :provide-specials #{'$d}
              :owned-vars #{'$d}
              :must-let-vars #{'$d}}

    (qslice/qslice
     :require ['$]
     :where '[[$d ?c] (rule-name ?d)]
     :provide '[$d])
    #::qslice{:require-specials #{'$ '%}
              :provide-specials #{'$d}
              :owned-vars #{'$d}
              :must-let-vars #{'$d}}))

(deftest compiled-query
  (is
   (= {:query       '{:find [?a] :in [?a] :where []}
       :args        [1]
       :slice-order [{:slice-idx 0 :name "" :selectivity 0}
                     {:slice-idx 1 :name "" :selectivity 0}]}
      (qslice/compiled-query
       [(qslice/qslice :provide '[?a] :let '{?a 1})
        (qslice/qslice :require '[?a])]
       '[?a])))


  (is
   (= '{:query {:find [?c] :in [$] :where [[?a:0:1 ?b:1:1 ?c]]}
        :args [db]
        :slice-order [{:slice-idx 0 :name $ :selectivity 0}
                      {:slice-idx 1 :name "" :selectivity 0}]}
      (qslice/compiled-query
       [(qslice/db-qslice 'db)
        (qslice/qslice :where '[[?a ?b ?c]] :provide '[?c])]
       '[?c])))

  (is
   (= '{:query {:find [?b ?c] :in [$] :where [[?a:0:1 ?b ?c]]}
        :args [db]
        :slice-order [{:slice-idx 0 :name $ :selectivity 0}
                      {:slice-idx 1 :name "" :selectivity 0}]}
      (qslice/compiled-query
       [(qslice/db-qslice 'db)
        (qslice/qslice :where '[[?a ?b ?c]] :provide '[?b ?c])]
       '{:find [?b ?c]})))

  (is
   (= '{:query {:find [?c] :with [?b] :in [$] :where [[?a:0:1 ?b ?c]]}
        :args [db]
        :slice-order [{:slice-idx 0 :name $ :selectivity 0}
                      {:slice-idx 1 :name "" :selectivity 0}]}
      (qslice/compiled-query
       [(qslice/db-qslice 'db)
        (qslice/qslice :where '[[?a ?b ?c]] :provide '[?b ?c])]
       '{:find [?c]
         :with [?b]})))

  ;; sort order of :in should be deterministic and pretty
  (let [q (qslice/compiled-query
           [(qslice/qslice :name :rel :provide '[?rel1 ?rel2] :let '{[?rel1 ?rel2] '[rel1 rel2]})
            (qslice/qslice :name :tuple :provide '[?tuple1 ?tuple2] :let '{[?tuple1 ?tuple2] '[tuple1 tuple2]})
            (qslice/qslice :name :coll :provide '[?coll] :let '{[?coll ...] '[coll]})
            (qslice/qslice :name :scalar2 :provide '[?scalar2] :let '{?scalar2 'scalar2})
            (qslice/qslice :name :scalar1 :provide '[?scalar1] :let '{?scalar1 'scalar1})
            (qslice/rule-qslice 'rules)
            (qslice/db-qslice 'db)
            (qslice/db-qslice '$h 'db)]
           '[?scalar1])
        in-clause (-> q :query :in)
        slice-order (mapv :name (:slice-order q))]
    (is (= '[$ $h % ?scalar1 ?scalar2 [?coll ...] [?rel1 ?rel2] [?tuple1 ?tuple2]] in-clause))
    ;; Note that slice order doesn't match in-clause order
    (is (= [:rel :tuple :coll :scalar2 :scalar1 '% '$ '$h] slice-order))))

(deftest compile-query-edge-cases
  (is
   (= '{:query
        {:find [?c]
         :in [$h ?a:0:1]
         :where [[$h ?a:0:1 ?b:1:1 ?c]
                 ($h or-join [?a:0:1]
                     ;; NOTE: ?b => ?b:1:1 here, even though this isn't
                     ;; actually the same var as the outer ?b:1:1
                     ;; due to or-join parameterization.
                     ;; This is still correct at runtime, but ugly.
                     ;; This also means we can't shade datasource vars.
                     [?a:0:1 ?b:1:1 ?c])]}
        :args        [db 1]
        :slice-order [{:slice-idx 0 :name $h :selectivity 0}
                      {:slice-idx 1 :name "" :selectivity 0}]}
      (qslice/compiled-query
       [(qslice/db-qslice '$h 'db)
        (qslice/qslice
         :let '{?a 1}
         :where '[[$h ?a ?b ?c]
                  ($h or-join [?a] [?a ?b ?c])]
         :provide '[?c])]
       '[?c]))))


(deftest where-clause-metadata
  ;; It's critical to preserve tag metadata for type hints in where clauses
  ;; for performance.
  (let [type-hint (-> (qslice/compiled-query
                       [(qslice/db-qslice '$ 'db)
                        (qslice/qslice
                         :let '{?a "string"}
                         :where '[[(str ?a "suffix") ?x]]
                         :provide '[?x])
                        (qslice/qslice
                         :where '[[(.equals ^java.lang.String ?x "foosuffix")]]
                         :provide '[?r])]
                       '[?r])
                      :query
                      :where
                      peek
                      first
                      second
                      meta
                      :tag)]
    (is (= 'java.lang.String type-hint))))

(deftest with-let-locked-no-must-let
  (let [qs (qslice/qslice :name "no-must-let" :where '[[?foo]])
        qs-locked (qslice/with-let-locked qs)
        qs-relocked (qslice/with-let-locked qs-locked)
        qs-locked-error (try (qslice/with-let qs-locked '?foo 1)
                             ::not-thrown
                             (catch Exception e
                               (::qslice/error (ex-data e))))]
    (is (::qslice/must-let-vars-checked? qs))
    (is (false? (qslice/let-locked? qs)))
    (is (::qslice/must-let-vars-checked? qs-locked))
    (is (true? (qslice/let-locked? qs-locked)))
    (is (= qs-locked qs-relocked))
    (is (= :qslice-let-locked qs-locked-error))))

(deftest with-let-locked-must-let
  (let [qs (qslice/qslice :name "must-let" :must-let '[?foo] :where '[[?foo]])
        qs-unlet-error (try (qslice/with-let-locked qs)
                            ::not-thrown
                            (catch Exception e
                              (::qslice/error (ex-data e))))
        qs-locked (-> qs
                      (qslice/with-let '?foo 1)
                      (qslice/with-let-locked))
        qs-relocked (qslice/with-let-locked qs-locked)
        qs-locked-error (try (qslice/with-let qs-locked '?foo 1)
                             ::not-thrown
                             (catch Exception e
                               (::qslice/error (ex-data e))))]
    (is (not (::qslice/must-let-vars-checked? qs)))
    (is (false? (qslice/let-locked? qs)))
    (is (= :unsatisfied-must-let qs-unlet-error))
    (is (::qslice/must-let-vars-checked? qs-locked))
    (is (true? (qslice/let-locked? qs-locked)))
    (is (= qs-locked qs-relocked))
    (is (= :qslice-let-locked qs-locked-error))))

(deftest or-qslice-errors
  (are [expected-error form]
       (= (try (qslice/or-qslice form) ::not-thrown
               (catch Exception e
                 (::qslice/error (ex-data e))))
          expected-error)
    :same-vars-not-provided [(qslice/qslice :provide '[?foo])
                             (qslice/qslice :provide '[?bar])]

    ;; Explicit datasource via :require
    :not-allowed-datasource     [(qslice/qslice :require '[$])
                                 (qslice/qslice :require '[$h])]
    :not-allowed-datasource     [(qslice/qslice :require '[$h])
                                 (qslice/qslice :require '[$h])]

    ;; Implicit datasources via :where
    :not-allowed-datasource [(qslice/qslice :where '[[?foo]])
                             (qslice/qslice :where '[[$h ?foo]])]
    :not-allowed-datasource [(qslice/qslice :where '[[$h ?foo]])
                             (qslice/qslice :where '[[$h ?foo]])]

    :unsatisfied-must-let [(qslice/qslice :must-let '[?foo]
                                          :where '[[?foo]])]))

(deftest or-qslice-name
  (let [qs (qslice/or-qslice [(qslice/qslice :name "s1")
                              (qslice/qslice :name "s2")])]
    (is (= "or(s1 s2)" (qslice/name qs)))))

(deftest or-qslice-providing
  (let [qs-db (qslice/db-qslice 'db)
        qs1 (qslice/qslice :provide '[?provided] :where '[[?provided ?a]])
        qs2 (qslice/qslice :provide '[?provided] :where '[[?provided ?a ?b]])]

    ;; Without any let binding
    (is (= '{:query {:find [?provided]
                     :in [$]
                     :where [(or-join [?provided]
                               [?provided ?a:0:0]
                               [?provided ?a:0:1 ?b:1:1])]}
             :args [db]}
           (-> (qslice/compiled-query
                [qs-db
                 (qslice/or-qslice [qs1 qs2])]
                '[?provided])
               (select-keys [:query :args]))))

    ;; With let binding on vars that are not must-let
    (is (= '{:query {:find [?provided]
                     :in [$ ?a:0:0:0:1 ?a:0:1:1:1]
                     :where [(or-join [[?a:0:0:0:1 ?a:0:1:1:1] ?provided]
                               [?provided ?a:0:0:0:1]
                               [?provided ?a:0:1:1:1 ?b:1:1])]}
             :args [db 1 2]}
           (-> (qslice/compiled-query
                [qs-db
                 (qslice/or-qslice
                  [(qslice/with-let qs1 '?a 1)
                   (qslice/with-let qs2 '?a 2)])]
                '[?provided])
               (select-keys [:query :args]))))))

(deftest or-qslice-requiring
  (let [qs-db (qslice/db-qslice 'db)
        qs-required (qslice/qslice :provide '[?required] :let '[[?required :required]])
        qs1 (qslice/qslice :require '[?required] :where '[[?required ?a]])
        qs2 (qslice/qslice :require '[?required] :where '[[?required ?a ?b]])]

    ;; Without any let-binding
    (is (= '{:query {:find [?required]
                     :in [$ ?required]
                     :where [(or-join [[?required]]
                               [?required ?a:0:0]
                               [?required ?a:0:1 ?b:1:1])]}
             :args  [db :required]}
           (-> (qslice/compiled-query
                [qs-db
                 qs-required
                 (qslice/or-qslice [qs1 qs2])]
                '[?required])
               (select-keys [:query :args]))))

    ;; With let binding on vars that are not must-let
    (is (= '{:query {:find [?required]
                     :in [$ ?a:0:0:0:2 ?a:0:1:1:2 ?required]
                     :where [(or-join [[?a:0:0:0:2 ?a:0:1:1:2 ?required]]
                               [?required ?a:0:0:0:2]
                               [?required ?a:0:1:1:2 ?b:1:1])]}
             :args [db 1 2 :required]}
           (-> (qslice/compiled-query
                [qs-db
                 qs-required
                 (qslice/or-qslice
                  [(qslice/with-let qs1 '?a 1)
                   (qslice/with-let qs2 '?a 2)])]
                '[?required])
               (select-keys [:query :args]))))))

(deftest or-qslice-complex-where
  (let [qs-db (qslice/db-qslice 'db)
        qs-rule (qslice/rule-qslice '[])
        qs-required (qslice/qslice :provide '[?required] :let '[[?required :required]])
        qs1 (qslice/qslice :where '[(not (rule-name ?a ?b))
                                    [(ground 1) ?a]])
        qs2 (qslice/qslice :where '[(or-join [[?a ?b] ?c]
                                      (and [?a ?b] [?b ?c])
                                      (and [?c ?b]))])

        qs3 (qslice/qslice :require '[?required]
                           :where '[[?a :attr1 ?required]
                                    [?a :attr2 ?b]
                                    [?b :attr1 ?required]])]
    ;; Without any let-binding
    (is (= '{:query {:find [?required]
                     :in [$ % ?required]
                     :where [(or-join
                               [[?required]]
                               (and
                                (not (rule-name ?a:0:0 ?b:1:0))
                                [(ground 1) ?a:0:0])
                               (or-join [[?a:0:1 ?b:1:1] ?c:2:1]
                                 (and
                                  [?a:0:1 ?b:1:1]
                                  [?b:1:1 ?c:2:1])
                                 (and
                                  [?c:2:1 ?b:1:1]))
                               (and
                                [?a:0:2 :attr1 ?required]
                                [?a:0:2 :attr2 ?b:1:2]
                                [?b:1:2 :attr1 ?required]))]}
             :args  [db [] :required]}
           (-> (qslice/compiled-query
                [qs-db
                 qs-rule
                 qs-required
                 (qslice/or-qslice [qs1 qs2 qs3])]
                '[?required])
               (select-keys [:query :args]))))))
