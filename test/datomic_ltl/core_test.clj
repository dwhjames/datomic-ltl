(ns datomic-ltl.core-test
  (:require [clojure.set :as set]
            [clojure.test :refer :all]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer [defspec]]
            [datomic.api :as d]
            [datomic-ltl.core :refer :all]))


(def ^:dynamic *conn*
  "A dynamic var to hold the Datomic connection."
  nil)


(def test-schema
  '[{:db/id #db/id [:db.part/db]
     :db/ident :user/props
     :db/valueType :db.type/keyword
     :db/cardinality :db.cardinality/many
     :db.install/_attribute :db.part/db}])


(defn my-fixture
  [f]
  (let [uri (str "datomic:mem://" (d/squuid))]
    (d/create-database uri)
    (let [c (d/connect uri)]
      @(d/transact c test-schema)
      (binding [*conn* c]
        (f)))
    (d/delete-database uri)))


(use-fixtures :once my-fixture)


(def propositions
  #{:a :b :c})


(defn gen-tx-data
  [curr size]
  (if (= size 0)
    (gen/return '())
    (gen/bind
     (if (seq curr)
       (gen/frequency [[3 (gen/return #{})]
                       [1 (gen/fmap hash-set
                                    (gen/elements curr))]])
       (gen/return #{}))
     (fn [retractions]
       (let [s1 (set/difference curr retractions)]
         (gen/bind
          (gen/fmap set
                    (gen/vector (gen/elements (set/difference propositions
                                                              retractions))
                                0
                                (count propositions)))
          (fn [assertions]
            (let [s2 (set/union s1 assertions)
                  gen-rest-tx-data
                  (gen/resize (dec size)
                              (gen/sized (partial gen-tx-data s2)))]
              (gen/fmap #(cons {:retract retractions
                                :assert assertions} %)
                        gen-rest-tx-data)))))))))


(def gen-init-tx-data
  (gen/bind
   (gen/elements propositions)
   (fn [init-val]
     (gen/fmap #(vector init-val %)
               (gen/sized (partial gen-tx-data #{init-val}))))))


(def gen-pred
  (gen/frequency [[1
                   (gen/fmap (fn [b]
                               (reify clojure.lang.IFn
                                 (toString [this] (str "constantly " b))
                                 (invoke [this x] b)))
                             gen/boolean)]
                  [9
                   (gen/fmap
                    (fn [elem]
                      (reify clojure.lang.IFn
                        (toString [this] (str "test for " elem))
                        (invoke [this coll] (some #{elem} coll))))
                    (gen/elements propositions))]]))


(defn build-db
  [init-val asserts-retracts]
  (let [tid (d/tempid :db.part/user)
        tx1 (-> *conn*
                d/db
                (d/with [[:db/add tid :user/props init-val]]))
        db1 (:db-after tx1)
        start-t (d/basis-t db1)
        eid (d/resolve-tempid db1 (:tempids tx1) tid)
        ]
    [(reduce (fn [db ars]
               (-> db
                   (d/with (concat
                            (map #(vector :db/add eid :user/props %)
                                 (:assert ars))
                            (map #(vector :db/retract eid :user/props %)
                                 (:retract ars))))
                   :db-after))
             db1
             asserts-retracts)
     start-t
     eid]))


(defn compute-final-set
  [init-val asserts-retracts]
  (reduce (fn [s ars]
            (set/union (set/difference s (:retract ars))
                       (:assert ars)))
          #{init-val}
          asserts-retracts))


;; check that `build-db` correctly constructs the initial
;; state of the db value
(defspec check-initial-db
  (prop/for-all
   [v gen-init-tx-data]
   (let [[init-val _] v
         [db t1 eid] (apply build-db v)]
     (= (-> db
            (d/as-of t1)
            (d/entity eid)
            :user/props
            set)
        #{init-val}))))


;; check that `build-db` correctly constructs the final
;; state of the db value
(defspec check-final-db
  (prop/for-all
   [v gen-init-tx-data]
   (let [[init-val asserts-retracts] v
         [db t1 eid] (apply build-db v)]
     (= (-> db
            (d/entity eid)
            :user/props
            set)
        (compute-final-set init-val asserts-retracts)))))


;; ## One-step of LTL temporal operators

;; G ɸ ≡ ɸ ∧ (X (G ɸ))
(defspec globally-one-step
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-globally db t1 eid :user/props p))
        (boolean
         (and
          (ltl-at-t db t1 eid :user/props p)
          (ltl-globally db (inc t1) eid :user/props p)))))))


;; F ɸ ≡ ɸ ∨ (X (F ɸ))
(defspec eventually-one-step
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-eventually db t1 eid :user/props p))
        (boolean
         (or
          (ltl-at-t db t1 eid :user/props p)
          (ltl-eventually db (inc t1) eid :user/props p)))))))


;; ɸ U ψ ≡ ψ ∨ (ɸ ∧ (X (ɸ U ψ)))
(defspec until-one-step
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred
    q gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-until db t1 eid :user/props p q))
        (boolean
         (or
          (ltl-at-t db t1 eid :user/props q)
          (and
           (ltl-at-t db t1 eid :user/props p)
           (ltl-until db (inc t1) eid :user/props p q))))))))


;; ɸ W ψ ≡ ψ ∨ (ɸ ∧ (X (ɸ W ψ)))
(defspec weak-until-one-step
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred
    q gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-weak-until db t1 eid :user/props p q))
        (boolean
         (or
          (ltl-at-t db t1 eid :user/props q)
          (and
           (ltl-at-t db t1 eid :user/props p)
           (ltl-weak-until db (inc t1) eid :user/props p q))))))))


;; ɸ R ψ ≡ ψ ∧ (ɸ ∨ (X (ɸ R ψ)))
(defspec release-one-step
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred
    q gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-release db t1 eid :user/props p q))
        (boolean
         (and
          (ltl-at-t db t1 eid :user/props q)
          (or
           (ltl-at-t db t1 eid :user/props p)
           (ltl-release db (inc t1) eid :user/props p q))))))))


;; ## Important equivalences between LTL formulas
;;
;; Logic in Computer Science : Modelling and Reasoning about Systems
;; Second Edition
;; Michael Huth and Mark Ryan
;; § 3.2.4

;; ¬ (G ɸ) ≡ F (¬ ɸ)
(defspec eventually-globally-dual-1
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (not
         (ltl-globally db t1 eid :user/props p))
        (boolean
         (ltl-eventually db t1 eid :user/props (comp not p)))))))


;; ¬ (F ɸ) ≡ G (¬ ɸ)
(defspec eventually-globally-dual-2
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (not
         (ltl-eventually db t1 eid :user/props p))
        (boolean
         (ltl-globally db t1 eid :user/props (comp not p)))))))


;; ¬ (X ɸ) ≡ X (¬ ɸ)
(defspec next-self-dual
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (not
         (ltl-next-t db t1 eid :user/props p))
        (boolean
         (ltl-next-t db t1 eid :user/props (comp not p)))))))


;; ¬ (ɸ U ψ) ≡ (¬ ɸ) R (¬ ψ)
(defspec until-release-dual-1
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred
    q gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (not
         (ltl-until db t1 eid :user/props p q))
        (boolean
         (ltl-release db t1 eid :user/props
                      (comp not p)
                      (comp not q)))))))


;; ¬ (ɸ R ψ) ≡ (¬ ɸ) U (¬ ψ)
(defspec until-release-dual-2
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred
    q gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (not
         (ltl-release db t1 eid :user/props p q))
        (boolean
         (ltl-until db t1 eid :user/props
                    (comp not p)
                    (comp not q)))))))


;; F (ɸ ∨ ψ) ≡ (F ɸ) ∨ (F ψ)
(defspec eventually-distributes-over-or
  (prop/for-all
   [v gen-init-tx-data
    p1 gen-pred
    p2 gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-eventually db t1 eid :user/props
                         #(or (p1 %) (p2 %))))
        (boolean
         (or
          (ltl-eventually db t1 eid :user/props p1)
          (ltl-eventually db t1 eid :user/props p2)))))))


;; G (ɸ ∧ ψ) ≡ (G ɸ) ∧ (G ψ)
(defspec globally-distributes-over-and
  (prop/for-all
   [v gen-init-tx-data
    p1 gen-pred
    p2 gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-globally db t1 eid :user/props
                       #(and (p1 %) (p2 %))))
        (boolean
         (and
          (ltl-globally db t1 eid :user/props p1)
          (ltl-globally db t1 eid :user/props p2)))))))


;; ρ U (ɸ ∨ ψ) ≡ (ρ U ɸ) ∨ (ρ U ψ)
(defspec until-right-distribute-over-or
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred
    q gen-pred
    r gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-until db t1 eid :user/props
                    p
                    #(or (q %)
                         (r %))))
        (boolean
         (or
          (ltl-until db t1 eid :user/props p q)
          (ltl-until db t1 eid :user/props p r)))))))


;; (ɸ ∧ ψ) U ρ ≡ (ɸ U ρ) ∧ (ψ U ρ)
(defspec until-left-distribute-over-and
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred
    q gen-pred
    r gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-until db t1 eid :user/props
                    #(and (p %)
                          (q %))
                    r))
        (boolean
         (and
          (ltl-until db t1 eid :user/props p r)
          (ltl-until db t1 eid :user/props q r)))))))


;; F ɸ ≡ ⊤ U ɸ
(defspec eventually-degenerate-until
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-eventually db t1 eid :user/props p))
        (boolean
         (ltl-until db t1 eid :user/props
                    (constantly true)
                    p))))))


;; G ɸ ≡ ⊥ R ɸ
(defspec globally-degenerate-release
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-globally db t1 eid :user/props p))
        (boolean
         (ltl-release db t1 eid :user/props
                      (constantly false)
                      p))))))


;; ɸ U ψ ≡ (ɸ W ψ) ∧ (F ψ)
(defspec until-in-terms-of-weak-until-and-eventually
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred
    q gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-until db t1 eid :user/props p q))
        (boolean
         (and
          (ltl-weak-until db t1 eid :user/props p q)
          (ltl-eventually db t1 eid :user/props q)))))))


;; ɸ W ψ ≡ (ɸ U ψ) ∨ (G ɸ)
(defspec weak-until-in-terms-of-until-and-globally
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred
    q gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-weak-until db t1 eid :user/props p q))
        (boolean
         (or
          (ltl-until db t1 eid :user/props p q)
          (ltl-globally db t1 eid :user/props p)))))))


;; ɸ W ψ ≡ ɸ R (ɸ ∨ ψ)
(defspec weak-until-in-terms-of-release
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred
    q gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-weak-until db t1 eid :user/props p q))
        (boolean
         (ltl-release db t1 eid :user/props
                      q
                      #(or (p %) (q %))))))))


;; ɸ R ψ ≡ ɸ W (ɸ ∧ ψ)
(defspec release-in-terms-of-weak-until
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred
    q gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-release db t1 eid :user/props p q))
        (boolean
         (ltl-weak-until db t1 eid :user/props
                         q
                         #(and (p %) (q %))))))))


;; Theorem 3.10
;; ɸ U ψ ≡ (¬ ((¬ ψ) U ((¬ ɸ) ∧ (¬ ψ)))) ∧ (F ψ)
(defspec theorem-3-10
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred
    q gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     (= (boolean
         (ltl-until db t1 eid :user/props p q))
        (boolean
         (and
          (not
           (ltl-until db t1 eid :user/props
                      (comp not q)
                      #(and (not (p %))
                            (not (q %)))))
          (ltl-eventually db t1 eid :user/props q)))))))


;; Remark 3.7
;; The future includes the present
;;
;; (G ɸ) → ɸ ≡ ⊤
(defspec future-includes-the-present-1
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     ;; ɸ → ψ ≡ (¬ ɸ) ∨ ψ
     (= (boolean
         (or
          (not (ltl-globally db t1 eid :user/props p))
          (ltl-at-t db t1 eid :user/props p)))
        true))))


;; ɸ → (ψ U ɸ) ≡ ⊤
(defspec future-include-the-present-2
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred
    q gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     ;; ɸ → ψ ≡ (¬ ɸ) ∨ ψ
     (= (boolean
         (or
          (not (ltl-at-t db t1 eid :user/props p))
          (ltl-until db t1 eid :user/props q p)))
        true))))


;; ɸ → (F ɸ) ≡ ⊤
(defspec future-include-the-present-3
  (prop/for-all
   [v gen-init-tx-data
    p gen-pred]
   (let [[db t1 eid] (apply build-db v)]
     ;; ɸ → ψ ≡ (¬ ɸ) ∨ ψ
     (= (boolean
         (or
          (not (ltl-at-t db t1 eid :user/props p))
          (ltl-eventually db t1 eid :user/props p)))
        true))))
