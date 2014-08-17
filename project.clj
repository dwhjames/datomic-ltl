(defproject datomic-ltl "0.1.0-SNAPSHOT"
  :description "An interpretation of LTL for Datomic"
  :url "https://github.com/dwhjames/datomic-ltl"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :dependencies [[org.clojure/clojure "1.6.0"]
                 [com.datomic/datomic-free "0.9.4815.12"]
                 [org.clojure/test.check "0.5.9" :scope "test"]])
