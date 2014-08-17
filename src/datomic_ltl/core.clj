;; ## Temporal operators for querying Datomic
;;
;; The core namespace contains implementations of the temporal
;; operators in Linear Temporal Logic.
(ns datomic-ltl.core
  (:require [datomic.api :as d]))


;; ---

;; ### Internal helper functions

(defn- rhistory
  "A reduction function that produces a map from transaction
   entity ids to the assertions and retractions that occured
   in that transaction.

       {12345
        {:added (:a :b)
         :removed (:c :d)}
        12346}

   The lists of values that were added and removed will be at
   most one if the associated attribute is `:db.cardinality/one`"
  [m d]
  (update-in m
             [(:tx d)
              (if (:added d)
                :added
                :removed)]
             #(conj % (:v d))))


(defn- datoms-ea
  "Fetch a lazy sequence of datoms from the `:eavt` index of
   the given database value `db`, using `e` and `a` as the
   entity id and attribute components, respectively."
  [db e a]
  (-> db
      (d/datoms :eavt e a)
      seq))


(defn- lookup-cardinality
  "Lookup the cardinality that is defined in the schema
   of database value `db` for the attribute `attr`. This
   will return one of

   - `:db.cardinality/one`
   - `:db.cardinality/many`"
  [db attr]
  (-> db
      (d/entity attr)
      :db/cardinality))


(defn- lift-p
  "Lift a predicate function `p` according to a cardinality.
   The lifted function expects to receive a set as an
   argument.

   In the `:db.cardinality/one` case, the set is expected to
   have at most one element. Therefore, the predicate `p` is
   invoked with the `first` element of the set, which could
   be `nil`.

  In the `:db.cardinality/many` case, the predicate `p` will
  be invoked with the received set, which could be empty."
  [p card]
  (case card
    :db.cardinality/one
    #(p (first %))
    :db.cardinality/many
    #(p %)))


;; ---

;; ## LTL point operators
;;
;; The point operators evaluate at a specific point, which
;; in Datomic terms means we observe the database as of a
;; a basis-t point.

(defn ltl-now
  "Test predicate `p` on the current value(s) for attribute
   `a` for entity `e` in database `db`.

   This returns the result of predicate `p`."
  [db e a p]
  (let [card (lookup-cardinality db a)
        p1 (lift-p p card)]
    (->> (datoms-ea db e a)
         (map :v)
         set
         p1)))


(defn ltl-at-t
  "Test predicate `p` on the value(s) for attribute `a` for
   entity `e` in database `db` as of basis-t point `t`.

   This returns the result of predicate `p`."
  [db t e a p]
  (ltl-now (d/as-of db t) e a p))


(defn ltl-next-t
  "Test predicate `p` on the value(s) for attribute `a` for
   entity `e` in database `db` as of basis-t point `t+1`.

  This returns the result of predicate `p`."
  [db t e a p]
  (ltl-at-t db (inc t) e a p))


;; ---

;; ### More internal helper functions

(defn- v-set-as-of
  "Fetch the set of values for attribute `a` for entity `e`
   in database `db` as of basis-t point `t`."
  [db t e a]
  (->> (-> db
           (d/as-of t)
           (datoms-ea e a))
       (map :v)
       set))


(defn- next-set
  "Compute a new set, starting from set `s`, removing all
   elements in `removed` and addding all elements in `added`."
  [s added removed]
  (reduce conj
          (reduce disj
                  s
                  removed)
          added))


;; ---

;; ## LTL path operators
;;
;; The path operators evaluate not just at a single point,
;; but at all points along a path. These operators require
;; a basis-t point that identifies the start of the path
;; and the path extends to the current basis-t of the given
;; database value.

(defn ltl-globally
  "Test the predicate `p` on the value(s) for attribute `a` for
   entity `e` in database `db` beginning at basis-t point `t`.

  Returns true if the predicate `p` is satisfied globally, that
  is to say `p` is satisfied as of all basis-t points greater
  than or equal to `t`. Otherwise, logical false."
  [db t e a p]
  (let [card (lookup-cardinality db a)
        p1 (lift-p p card)
        initial-set (v-set-as-of db t e a)]
    (and
     (p1 initial-set)
     (if-let [datoms (-> db
                         (d/since t)
                         d/history
                         (datoms-ea e a))]
       (loop [hist (->> datoms
                        (reduce rhistory (sorted-map))
                        seq)
              prev-set initial-set]
         (or
          (not hist)
          (let [[tx {:keys [added removed]}] (first hist)
                curr-set (next-set prev-set added removed)]
            (and (p1 curr-set)
                 (recur (next hist) curr-set)))))
       true))))


(defn ltl-eventually
  "Test the predicate `p` on the value(s) for attribute `a` for
   entity `e` in database `db` beginning at basis-t point `t`.

   Returns a vector of the basis-t and the logical truth value of
   the *first* point (greater than or equal to `t`) that satisfies
   the predicate. Otherwise, logical false."
  [db t e a p]
  (let [card (lookup-cardinality db a)
        p1 (lift-p p card)
        initial-set (v-set-as-of db t e a)]
    (or
     (when-let [r (p1 initial-set)]
       [t r])
     (when-let [datoms (-> db
                           (d/since t)
                           d/history
                           (datoms-ea e a))]
       (loop [hist (->> datoms
                        (reduce rhistory (sorted-map))
                        seq)
              prev-set initial-set]
         (when hist
           (let [[tx {:keys [added removed]}] (first hist)
                 curr-set (next-set prev-set added removed)]
             (or
                (when-let [r (p1 curr-set)]
                  [(d/tx->t tx) r])
                (recur (next hist) curr-set)))))))))


(defn ltl-eventually-globally
  "Test the predicate `p` on the value(s) for attribute `a` for
   entity `e` in the database `db` beginning at basis-t point `t`.

   Returns the least basis-t greater than or equal to `t` for which
   the `globally` operator holds from that basis-t. Otherwise,
   logical false."
  [db t e a p]
  (loop [[t1 _] (ltl-eventually db t e a p)]
    (cond
     (not t1) false
     (ltl-globally db t1 e a p) t1
     :else (recur (ltl-eventually db (inc t1) e a p)))))


(defn ltl-until
  "Test predicates `p` and `q` on the value(s) for attribute `a` for
   entity `e` in the database `db` beginning at basis-t point `t`.

   This operator tests if `p` holds until `q` holds. Furthermore, `q`
   must eventually hold.

   Returns a vector of the basis-t and the logical truth value of
   the *first* point (greater than or equal to `t`) that satisfies
   predicate `q` **and** where `p` has been continually satisfied
   previous to that point. Otherwise, logical false."
  [db t e a p q]
  (let [card (lookup-cardinality db a)
        p1 (lift-p p card)
        q1 (lift-p q card)
        initial-set (v-set-as-of db t e a)]
    (or
     (when-let [r (q1 initial-set)]
       [t r])
     (and
      (p1 initial-set)
      (when-let [datoms (-> db
                            (d/since t)
                            d/history
                            (datoms-ea e a))]
        (loop [hist (->> datoms
                         (reduce rhistory (sorted-map))
                         seq)
               prev-set initial-set]
          (when hist
            (let [[tx {:keys [added removed]}] (first hist)
                  curr-set (next-set prev-set added removed)]
              (if-let [r (q1 curr-set)]
                [(d/tx->t tx) r]
                (when (p1 curr-set)
                  (recur (next hist) curr-set)))))))))))


(defn ltl-weak-until
  "Test predicates `p` and `q` on the value(s) for attribute `a` for
   entity `e` in the database `db` beginning at basis-t point `t`.

   This is the *weak* form of `until`. This operator tests if `p`
   holds until `q` holds, allowing for the case where `q` never holds
   as long as `p` always did.

   Returns a vector of the basis-t and the logical truth value of
   the *first* point (greater than or equal to `t`) that satisfies
   `q` **and** where `p` has been continually satisfied previous to
   that point. Or, `:weak` if `q` is never satsified, but `p` has
   been globally satisfied. Otherwise, logical false."
  [db t e a p q]
  (let [card (lookup-cardinality db a)
        p1 (lift-p p card)
        q1 (lift-p q card)
        initial-set (v-set-as-of db t e a)]
    (or
     (when-let [r (q1 initial-set)]
       [t r])
     (and
      (p1 initial-set)
      (if-let [datoms (-> db
                          (d/since t)
                          d/history
                          (datoms-ea e a))]
        (loop [hist (->> datoms
                         (reduce rhistory (sorted-map))
                         seq)
               prev-set initial-set]
          (if hist
            (let [[tx {:keys [added removed]}] (first hist)
                  curr-set (next-set prev-set added removed)]
              (if-let [r (q1 curr-set)]
                [(d/tx->t tx) r]
                (when (p1 curr-set)
                  (recur (next hist) curr-set))))
            :weak))
        :weak)))))


(defn ltl-release
  "Test predicates `p` and `q` on the value(s) for attribute `a` for
   entity `e` in the database `db` beginning at basis-t point `t`.

   This operator tests if `p` is ever satisfied to *release* the
   requirement for `q` to be satisfied any further. If no release
   occurs then `q` must be globally satisfied.

   Returns the basis-t of the *first* point (greater than or equal
   to `t`) that satisfies `p` **and** where `q` has been continu
   predicate `q` **and** where `p` has been continually satisfied
   up until and including that point. Or, `:unreleased` if `p`
   is never satisfied, but `q` has been globally satisfied.
   Otherwise, logical false."
  [db t e a p q]
  (let [card (lookup-cardinality db a)
        p1 (lift-p p card)
        q1 (lift-p q card)
        initial-set (v-set-as-of db t e a)]
    (and
     (q1 initial-set)
     (or
      (p1 initial-set)
      (if-let [datoms (-> db
                          (d/since t)
                          d/history
                          (datoms-ea e a))]
        (loop [hist (->> datoms
                         (reduce rhistory (sorted-map))
                         seq)
               prev-set initial-set]
          (if hist
            (let [[tx {:keys [added removed]}] (first hist)
                  curr-set (next-set prev-set added removed)]
              (when (q1 curr-set)
                (if (p1 curr-set)
                  (d/tx->t tx)
                  (recur (next hist) curr-set))))
            :unreleased))
        :unreleased)))))

