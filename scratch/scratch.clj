
(require '[datomic.api :as d])

(def uri "datomic:mem://ltl")

(d/create-database uri)

(def conn (d/connect uri))

(def schema
  '[{:db/id #db/id [:db.part/db]
     :db/ident :user/email
     :db/valueType :db.type/string
     :db/cardinality :db.cardinality/many
     :db/doc "A user's email address"
     :db.install/_attribute :db.part/db}])

@(d/transact conn schema)

(defn mk-user
  [name email]
  (let [user-tempid (d/tempid :db.part/user)
        tx @(d/transact conn
                        [{:db/id user-tempid
                          :user/email email}])]
    (d/resolve-tempid (:db-after tx) (:tempids tx) user-tempid)))

(def alice
  (mk-user "alice" "alice@hotmail.com"))

(-> conn d/db d/basis-t)

(def tx-datas
  [[[:db/add alice :user/email "alice@yahoo.com"]]
   [[:db/add alice :user/email "alice@gmail.com"]]
   [[:db/retract alice :user/email "alice@yahoo.com"]]
   [[:db/add alice :user/email "alice@outlook.com"]
    [:db/retract alice :user/email "alice@hotmail.com"]]])

(doseq [tx-data tx-datas]
  @(d/transact conn tx-data))

(defn query-email
  [db user]
  (d/q '[:find ?t ?added ?email
         :in $ ?user
         :where
         [?user :user/email ?email ?tx ?added]
         [(datomic.api/tx->t ?tx) ?t]]
       db
       user))

(defn value-history
  [e a]
  (->> (-> conn
           d/db
           d/history
           (d/datoms :eavt e a)
           seq)
       (reduce (fn [m d]
                 (update-in m
                            [(d/tx->t (:tx d))
                             (if (:added d)
                               :added
                               :removed)]
                            #(conj % (:v d))))
               (sorted-map))))

(value-history alice :user/email)

(require '[datomic-ltl.core :as ltl])

;; alice's email addresses always start with "alice"
(ltl/globally (d/db conn) 1000 alice :user/email
              (fn [t v]
                (every? #(.startsWith % "alice")
                        v)))
;; true

;; eventually alice gets a gmail address
(ltl/eventually (d/db conn) 1000 alice :user/email
                #(contains? %2 "alice@gmail.com"))
;; at basis-t 1004

;; alice has a hotmail address from basis-t 1001
;; until she gets an outlook address
(ltl/until (d/db conn) 1001 alice :user/email
           #(contains? %2 "alice@hotmail.com")
           #(contains? %2 "alice@outlook.com"))
;; at basis-t 1006

;; alice always has at least one email address from basis-t 1001
;; until (weakly) she gets a facebook address
(ltl/weak-until (d/db conn) 1001 alice :user/email
                #(> (count %2) 0)
                #(contains? %2 "alice@facebook.com"))
;; but she never got a facebook address,
;; and thus never gave up on email

;; alice, from basis-t 1001 has a hotmail address
;; up to and including the point that she has 3 addresses
(ltl/release (d/db conn) 1001 alice :user/email
             #(= 3 (count %2))
             #(contains? %2 "alice@hotmail.com"))
;; at basis-t 1004
