(ns clojure.compiler.helpers
  (:use [clojure.runtime :only (lookup-var)]))

(defn lookup-var-in-current-ns [sym]
  (let [v (lookup-var sym true)]
    (if (nil? v)
      (throw (RuntimeException. "Can't refer to qualified var that doesn't exist"))
      (if (not (= (namespace v) *ns*))
        (if (nil? (namespace sym))
          (.intern *ns* sym)
          (throw (RuntimeException. "Can't create defs outside of current ns")))))))

