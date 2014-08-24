;; ## Temporal operators for querying Datomic
;;
;; The core namespace contains implementations of the temporal
;; operators in Linear Temporal Logic.
;;
;; ## Theory
;;
;; To begin, we must define terms and give a precise
;; characterization of how LTL can be interpreted in Datomic.
;;
;; The following definitions are taken from:
;;
;; > Michael Huth and Mark Ryan,
;; > *Logic in Computer Science* -
;; > *Modelling and Reasoning about Systems*,
;; > Second Edition,
;; > Cambridge University Press, 2004.
;; > (pp. 178-182)
;;
;;
;; ### Definition 3.4
;;
;; A transition system \\( \mathcal{M} = (S, \rightarrow, L) \\)
;; is a set of states \\( S \\) endowed with a transition relation
;; \\( \rightarrow \\) (a binary relation in \\( S \\)), such
;; that every \\( s \in S \\) has some \\( s' \in S \\) with
;; \\( s \rightarrow s' \\), and a labelling function
;; \\( L : S \rightarrow \mathcal{P}(\mathtt{Atoms}) \\).
;;
;;
;; ### Interpretation of Definition 3.4 in Datomic
;;
;; We can interpet a Datomic database as a transition system that
;; is roughly analogous to Definition 3.4; however, it does break
;; a few rules. We can think of the set of states as the basis-t
;; points of the database. The transition relation is trivial, as
;; Datomic linearizes all transactions. For the database value `db`
;; constructed from `(d/db conn)`, i.e., the latest available
;; novelty, then let \\( t \\) be a valid basis-t value that is
;; *strictly less than* `(d/basis-t db)`. The next state is
;; `(d/next-t (d/as-of db t))`, which is \\( t + 1 \\). This is
;; transition relation. The fly in the ointment is that
;; `(d/next-t db)` is a basis-t point that identifies a state that
;; does not yet exists (hence the *strictly less than* above). This
;; next basis-t point identifies the database value that will exist
;; after the next transaction. The *every* in Definition 3.4 does
;; not hold, but a loose interpretation is arguably still useful.
;; Finally, the labelling function can be see as an abstract
;; function for looking up datoms in the database as of a point
;; in time (a state), where \\( \mathcal{P}(\mathtt{Atoms}) \\)
;; describes the value space of data than can be stored in Datomic.
;;
;;
;; ### Definition 3.5
;;
;; A path in a model \\( \mathcal{M} = (S, \rightarrow, L) \\)
;; is an infinite sequence of states
;; \\( s _{1}, s _{2}, s _{3}, \dots \\) in \\( S \\)
;; such that, for each \\( i \ge 1 \\),
;; \\( s _{i} \rightarrow s _{i+1} \\). We write the path as
;; \\( s _{1} \rightarrow s _{2} \rightarrow \dots \\).
;;
;;
;; ### Interpretation of Definition 3.5 in Datomic
;;
;; In Datomic, there can be no infinite sequence of states,
;; as the set of basis-t values is finite and the transition
;; relation is strictly increasing partial function on these
;; values. In plain terms, we can linearlly traverse the
;; history of the database, but we are bound by the novelty
;; that the peer is currently aware of.
;;
;; The means that some LTL formulas will have a degenerate
;; interpretation in Datomic. For example,
;; \\( \mathrm{G} ~ \mathrm{F} ~ \phi \\) expresses that
;; \\( \phi \\) is satisfied infinitely often along the
;; path in question. This is an example of a **liveness**
;; property, *something good keeps happening*. However,
;; as there are no infinite paths, there can be no
;; *infinitely often*. The useful LTL formulas will be the
;; ones that have a useful interpretation on finite paths.
;; For example, a **safety** property usually states that
;; *something bad never happens*, and is expressed as
;; \\( \mathrm{G} ~ \neg \phi \\). We can adjust that
;; interpretation for Datomic to say,
;; *something bad never happened*.
;;
;;
;; ### Definition 3.6
;;
;; Let \\( \mathcal{M} = (S, \rightarrow, L) \\) be a model and
;; \\( \pi = s_1 \rightarrow \dots \\) be a path in
;; \\( \mathcal{M} \\). Whether \\( \pi \\) satisfies an LTL
;; formula is defined by the satisfaction relation
;; \\( \vDash \\) as follows:
;;
;;   1. \\( \pi \vDash \top \\)
;;   2. \\( \pi \nvDash \bot \\)
;;   3. \\( \pi \vDash p \\) iff \\( p \in L(s_1) \\)
;;   4. \\( \pi \vDash \neg \phi \\)
;;      iff \\( \pi \nvDash \phi \\)
;;   5. \\( \pi \vDash \phi _{1} \wedge \phi _{2} \\)
;;      iff \\( \pi \vDash \phi _{1} \\)
;;      and \\( \pi \vDash \phi _{2} \\)
;;   6. \\( \pi \vDash \phi _{1} \vee \phi _{2} \\)
;;      iff \\( \pi \vDash \phi _{1} \\)
;;      or \\( \pi \vDash \phi _{2} \\)
;;   7. \\( \pi \vDash \phi _{1} \rightarrow \phi _{2} \\)
;;      iff \\( \pi \vDash \phi _{2} \\)
;;      whenever \\( \pi \vDash \phi _{1} \\)
;;   8. \\( \pi \vDash \mathrm{X} ~ \phi \\)
;;      iff \\( \pi^2 \vDash \phi \\)
;;   9. \\( \pi \vDash \mathrm{G} ~ \phi \\)
;;      iff, for all \\( i \ge 1, \pi^i \vDash \phi \\)
;;   10. \\( \pi \vDash \mathrm{F} ~ \phi \\)
;;       iff there is some \\( i \ge 1 \\)
;;       such that \\( \pi^i \vDash \phi \\)
;;   11. \\( \pi \vDash \phi ~ \mathrm{U} ~ \psi \\)
;;       iff there is some \\( i \ge 1 \\)
;;       such that \\( \pi^2 \vDash \psi \\)
;;       and for all \\( j = 1, \dots, i - 1 \\)
;;       we have \\( \pi^j \vDash \phi \\)
;;   12. \\( \pi \vDash \phi ~ \mathrm{W} ~ \psi \\)
;;       iff either there is some \\( i \ge 1 \\)
;;       such that \\( \pi^i \vDash \psi \\)
;;       and for all \\( j = 1, \dots, i - 1 \\)
;;       we have \\( \pi^j \vDash \phi \\);
;;       or for all \\( k \ge 1 \\)
;;       we have \\( \pi \vDash \phi \\)
;;   13. \\( \pi \vDash \phi ~ \mathrm{R} ~ \psi \\)
;;       iff either there is some \\( i \ge 1 \\)
;;       such that \\( \pi^i \vDash \phi \\)
;;       and for all \\( j = 1, \dots, i \\)
;;       we have \\( \pi^j \vDash \psi \\);
;;       or for all \\( k \ge 1 \\)
;;       we have \\( \pi \vDash \psi \\)
;;
;;
;; ### Definition 3.8
;;
;; Suppose \\( \mathcal{M} = (S, \rightarrow, L) \\) is a model,
;; \\( s \in S \\), and \\( \phi \\) and LTL formula. We write
;; \\( \mathcal{M}, s \vDash \phi \\) if, for every execution
;; path \\( \pi \\) of \\( \mathcal{M} \\) starting at
;; \\( s \\), we have \\( \pi \vDash \phi \\).
;;
;; ### Interpretations of Definitions 3.6 and 3.8 in Datomic
;;
;; As discussed above, paths in the Datomic interpretation are
;; finite; moreover, from any state there is exactly one path
;; as the transition relation defines at most one next state
;; at all states. Therefore, given a database value `db` we have
;; a model \\( \mathcal{M} \\), and given a basis-t point `t` we
;; have a state \\( s \\), so we have precise interpretation of
;; \\( \mathtt{db}, \mathtt{t} \vDash \phi \\) and the unique
;; path \\( \pi \\).
;;
(ns datomic-ltl.core
  (:require [datomic.api :as d]))


;; ---

;; ## Implementation

;; ### Internal helper functions

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
   The lifted function expects to receive a basis-t value
   and a set as an argument.

   In the `:db.cardinality/one` case, the set is expected to
   have at most one element. Therefore, the predicate `p` is
   invoked with the `first` element of the set, which could
   be `nil`.

   In the `:db.cardinality/many` case, the predicate `p` will
   be invoked with the received set, which could be empty."
  [p card]
  (case card
    :db.cardinality/one
    (fn [t arg]
      (p t (first arg)))
    :db.cardinality/many
    (fn [t arg]
      (p t arg))))



;; ---

;; ## LTL point operators
;;
;; The point operators evaluate at a specific point, which
;; in Datomic terms means we observe the database as of a
;; a basis-t point.

(defn now
  "Test predicate `p` on the current value(s) for attribute
   `a` for entity `e` in database `db`.

   This returns the result of predicate `p`."
  [db e a p]
  (let [card (lookup-cardinality db a)
        p1 (lift-p p card)]
    (->> (datoms-ea db e a)
         (map :v)
         set
         (p1 (d/basis-t db)))))


(defn at-t
  "Test predicate `p` on the value(s) for attribute `a` for
   entity `e` in database `db` as of basis-t point `t`.

   This returns the result of predicate `p`."
  [db t e a p]
  (now (d/as-of db t) e a p))


;; ### Temporal operator X (next)
;;
;; $$ \pi \vDash \mathrm{X} ~ \phi
;;    \text{ iff } \pi^2 \vDash \phi $$

(defn next-t
  "Test predicate `p` on the value(s) for attribute `a` for
   entity `e` in database `db` as of basis-t point `t+1`.

  This returns the result of predicate `p`."
  [db t e a p]
  (at-t db (inc t) e a p))


;; #### Self-duality of X
;;
;; $$ \neg \mathrm{X} ~ \phi \equiv
;;    \mathrm{X} ~ \neg \phi $$


;; ---

;; ### Internal helper functions to process the history of values

(defn- build-history
  "Given a lazy sequence of datoms extracted from a history
   database (for a particular entity and attribute), build
   a history of values that were added and removed, ordered
   by transaction entity id.

   The core computation of this function is a reduction of
   the datoms into a sorted map that maps transaction
   entity ids to the values that were asserted and retracted
   in that transaction. The intermediate datastructure looks
   like the following:

       {12345
        {:added (:a :b)
         :removed (:c :d)}
        12346
         {...}
        ...}

   The lists of values that were added and removed will be at
   most one if the associated attribute is `:db.cardinality/one`.

   This function returns a lazy sequence of this sorted map."
  [datoms]
  (->> datoms
       (reduce (fn [m datom]
                 (update-in m
                            [(:tx datom)
                             (if (:added datom)
                               :added
                               :removed)]
                            #(conj % (:v datom))))
               (sorted-map))
       seq))


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

;; ### Temporal operator G (globally)
;;
;; $$ \pi \vDash \mathrm{G} ~ \phi
;;    \text{ iff, for all } i \ge 1, \pi^i \vDash \phi $$

(defn globally
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
     (p1 t initial-set)
     (if-let [datoms (-> db
                         (d/since t)
                         d/history
                         (datoms-ea e a))]
       (loop [hist (build-history datoms)
              prev-set initial-set]
         (or
          (not hist)
          (let [[tx {:keys [added removed]}] (first hist)
                curr-set (next-set prev-set added removed)]
            (and (p1 (d/tx->t tx) curr-set)
                 (recur (next hist) curr-set)))))
       true))))


;; #### One-step semantics of G
;;
;; $$ \mathrm{G} ~ \phi \equiv
;;    \phi \wedge \mathrm{X} ~ \mathrm{G} ~ \phi $$
;;
;;
;; #### G distributes over conjunction
;;
;; $$ \mathrm{G} ~ (\phi \wedge \psi) \equiv
;;    \mathrm{G} ~ \phi \wedge \mathrm{G} ~ \psi $$
;;
;;
;; #### G includes the present
;;
;; $$ \mathrm{G} ~ \phi \rightarrow \phi \equiv \top $$


;; ### Temporal operator F (eventually)
;;
;; $$ \pi \vDash \mathrm{F} ~ \phi
;;    \text{ iff there is some } i \ge 1
;;    \text{ such that } \pi^i \vDash \phi $$

(defn eventually
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
     (when-let [r (p1 t initial-set)]
       [t r])
     (when-let [datoms (-> db
                           (d/since t)
                           d/history
                           (datoms-ea e a))]
       (loop [hist (build-history datoms)
              prev-set initial-set]
         (when hist
           (let [[tx {:keys [added removed]}] (first hist)
                 t1 (d/tx->t tx)
                 curr-set (next-set prev-set added removed)]
             (or
                (when-let [r (p1 t1 curr-set)]
                  [t1 r])
                (recur (next hist) curr-set)))))))))


;; #### One-step semantics of F
;;
;; $$ \mathrm{F} ~ \phi \equiv
;;    \phi \vee \mathrm{X} ~ \mathrm{F} ~ \phi $$
;;
;;
;; #### F distributes over disjunction
;;
;; $$ \mathrm{F} ~ (\phi \vee \psi) \equiv
;;    \mathrm{F} ~ \phi \vee \mathrm{F} ~ \psi $$
;;
;;
;; #### Duality of G and F
;;
;; $$ \neg \mathrm{G} ~ \phi \equiv
;;    \mathrm{F} ~ \neg \phi $$
;;
;; $$ \neg \mathrm{F} ~ \phi \equiv
;;    \mathrm{G} ~ \neg \phi $$
;;
;;
;; #### F includes the present
;;
;; $$ \phi \rightarrow \mathrm{F} ~ \phi \equiv \top $$



;; ### Temporal operator U (until)
;;
;; $$ \pi \vDash \phi ~ \mathrm{U} ~ \psi
;;    \text{ iff there is some } i \ge 1
;;    \text{ such that } \pi^2 \vDash \psi $$
;; $$ \text{ and for all } j = 1, \dots, i - 1
;;    \text{ we have } \pi^j \vDash \phi $$

(defn until
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
     (when-let [r (q1 t initial-set)]
       [t r])
     (and
      (p1 t initial-set)
      (when-let [datoms (-> db
                            (d/since t)
                            d/history
                            (datoms-ea e a))]
        (loop [hist (build-history datoms)
               prev-set initial-set]
          (when hist
            (let [[tx {:keys [added removed]}] (first hist)
                  t1 (d/tx->t tx)
                  curr-set (next-set prev-set added removed)]
              (if-let [r (q1 t1 curr-set)]
                [t1 r]
                (when (p1 t1 curr-set)
                  (recur (next hist) curr-set)))))))))))


;; #### One-step semantics of U
;;
;; $$ \phi ~ \mathrm{U} ~ \psi \equiv
;;    \psi \vee (\phi \wedge
;;    \mathrm{X} ~ (\phi ~ \mathrm{U} ~ \psi)) $$
;;
;;
;; #### U right-distributes over disjunction
;;
;; $$ \rho ~ \mathrm{U} ~ (\phi \vee \psi) \equiv
;;    (\rho ~ \mathrm{U} ~ \phi) \vee
;;    (\rho ~ \mathrm{U} ~ \psi) $$
;;
;;
;; #### U left-distributes over conjunction
;;
;; $$ (\phi \wedge \psi) ~ \mathrm{U} ~ \rho \equiv
;;    (\phi ~ \mathrm{U} ~ \rho) \wedge
;;    (\psi ~ \mathrm{U} ~ \rho) $$
;;
;;
;; #### F in terms of U
;;
;; $$ \mathrm{F} ~ \phi \equiv
;;    \top ~ \mathrm{U} ~ \phi $$
;;
;;
;; #### U includes the present
;;
;; $$ \phi \rightarrow (\psi ~ \mathrm{U} ~ \phi) \equiv \top $$


;; ### Temporal operator W (weak until)
;;
;; $$ \pi \vDash \phi ~ \mathrm{W} ~ \psi
;;    \text{ iff either there is some } i \ge 1 $$
;; $$ \text{ such that } \pi^i \vDash \psi \text{ and } $$
;; $$ \text{ for all } j = 1, \dots, i - 1
;;    \text{ we have } \pi^j \vDash \phi \text{;} $$
;; $$ \text{ or for all } k \ge 1
;;    \text{ we have } \pi \vDash \phi $$

(defn weak-until
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
     (when-let [r (q1 t initial-set)]
       [t r])
     (and
      (p1 t initial-set)
      (if-let [datoms (-> db
                          (d/since t)
                          d/history
                          (datoms-ea e a))]
        (loop [hist (build-history datoms)
               prev-set initial-set]
          (if hist
            (let [[tx {:keys [added removed]}] (first hist)
                  t1 (d/tx->t tx)
                  curr-set (next-set prev-set added removed)]
              (if-let [r (q1 t1 curr-set)]
                [t1 r]
                (when (p1 t1 curr-set)
                  (recur (next hist) curr-set))))
            :weak))
        :weak)))))


;; #### One-step semantics of W
;;
;; $$ \phi ~ \mathrm{W} ~ \psi \equiv
;;    \psi \vee (\phi \wedge
;;    \mathrm{X} ~ (\phi ~ \mathrm{W} ~ \psi)) $$
;;
;;
;; #### U in terms of W and F
;;
;; $$ \phi ~ \mathrm{U} ~ \psi \equiv
;;    (\phi ~ \mathrm{W} ~ \psi) \wedge
;;    \mathrm{F} ~ \psi $$
;;
;;
;; #### W in terms of U and G
;;
;; $$ \phi ~ \mathrm{W} ~ \psi \equiv
;;    (\phi ~ \mathrm{U} ~ \psi) \vee
;;    \mathrm{G} ~ \psi $$
;;
;; $$ \phi ~ \mathrm{W} ~ \psi \equiv
;;    \phi ~ \mathrm{U} ~ (\psi \vee
;;    \mathrm{G} ~ \psi) $$


;; ### Temporal operator R (release)
;;
;; $$ \pi \vDash \phi ~ \mathrm{R} ~ \psi
;;    \text{ iff either there is some } i \ge 1 $$
;; $$ \text{ such that } \pi^i \vDash \phi \text{ and } $$
;; $$ \text{ for all } j = 1, \dots, i
;;    \text{ we have } \pi^j \vDash \psi \text{;} $$
;; $$ \text{ or for all } k \ge 1
;;    \text{ we have } \pi \vDash \psi $$

(defn release
  "Test predicates `p` and `q` on the value(s) for attribute `a` for
   entity `e` in the database `db` beginning at basis-t point `t`.

   This operator tests if `p` is ever satisfied to *release* the
   requirement for `q` to be satisfied any further. If no release
   occurs then `q` must be globally satisfied.

   Returns the basis-t of the *first* point (greater than or equal
   to `t`) that satisfies `p` **and** where `q` has been continually
   satisfied up until and including that point. Or, `:unreleased`
   if `p` is never satisfied, but `q` has been globally satisfied.
   Otherwise, logical false."
  [db t e a p q]
  (let [card (lookup-cardinality db a)
        p1 (lift-p p card)
        q1 (lift-p q card)
        initial-set (v-set-as-of db t e a)]
    (and
     (q1 t initial-set)
     (or
      (p1 t initial-set)
      (if-let [datoms (-> db
                          (d/since t)
                          d/history
                          (datoms-ea e a))]
        (loop [hist (build-history datoms)
               prev-set initial-set]
          (if hist
            (let [[tx {:keys [added removed]}] (first hist)
                  t1 (d/tx->t tx)
                  curr-set (next-set prev-set added removed)]
              (when (q1 t1 curr-set)
                (if (p1 t1 curr-set)
                  t1
                  (recur (next hist) curr-set))))
            :unreleased))
        :unreleased)))))


;; #### One-step semantics of R
;;
;; $$ \phi ~ \mathrm{R} ~ \psi \equiv
;;    \psi \wedge (\phi \vee
;;    \mathrm{X} ~ (\phi ~ \mathrm{R} ~ \psi)) $$
;;
;;
;; #### Duality of U and R
;;
;; $$ \neg (\phi ~ \mathrm{U} ~ \psi) \equiv
;;    \neg \phi ~ \mathrm{R} ~ \neg \psi $$
;;
;; $$ \neg (\phi ~ \mathrm{R} ~ \psi) \equiv
;;    \neg \phi ~ \mathrm{U} ~ \neg \psi $$
;;
;;
;; #### G in terms of R
;;
;; $$ \mathrm{G} ~ \phi \equiv
;;    \bot ~ \mathrm{R} ~ \phi $$
;;
;;
;; #### W in terms of R
;;
;; $$ \phi ~ \mathrm{W} ~ \psi \equiv
;;    \phi ~ \mathrm{R} ~ (\phi \vee \psi) $$
;;
;;
;; #### R in terms of W
;;
;; $$ \phi ~ \mathrm{R} ~ \psi \equiv
;;    \phi ~ \mathrm{W} ~ (\phi \wedge \psi) $$
