(ns datomic-ltl.core
  (:require [datomic.api :as d]))


(defn- rhistory
  [m d]
  (update-in m
             [(:tx d)
              (if (:added d)
                :added
                :removed)]
             #(conj % (:v d))))


(defn- datoms-ea
  [db e a]
  (-> db
      (d/datoms :eavt e a)
      seq))


(defn- lookup-cardinality
  [db attr]
  (-> db
      (d/entity attr)
      :db/cardinality))


(defn- lift-p
  [p card]
  (case card
    :db.cardinality/one
    #(p (first %))
    :db.cardinality/many
    #(p %)))


(defn ltl-now
  [db e a p]
  (let [card (lookup-cardinality db a)
        p1 (lift-p p card)]
    (when-let [ds (datoms-ea db e a)]
      (->> ds
           (map :v)
           set
           p1))))


(defn ltl-at-t
  [db t e a p]
  (ltl-now (d/as-of db t) e a p))


(defn ltl-next-t
  [db t e a p]
  (ltl-at-t db (inc t) e a p))


(defn- v-set-as-of
  [db t e a]
  (->> (-> db
           (d/as-of t)
           (datoms-ea e a))
       (map :v)
       set))

(defn- next-set
  [s added removed]
  (reduce conj
          (reduce disj
                  s
                  removed)
          added))


(defn ltl-globally
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
  [db t e a p]
  (let [card (lookup-cardinality db a)
        p1 (lift-p p card)
        initial-set (v-set-as-of db t e a)]
    (or
     (when-let [r (p1 initial-set)]
       [t t])
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
  [db t e a p]
  (loop [[t1 _] (ltl-eventually db t e a p)]
    (cond
     (not t1) false
     (ltl-globally db t1 e a p) t1
     :else (recur (ltl-eventually db (inc t1) e a p)))))


(defn ltl-until
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

