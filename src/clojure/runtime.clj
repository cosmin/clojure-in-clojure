(ns clojure.runtime
  (:import [clojure.lang Symbol Namespace])
  (:import [java.io PrintWriter])
  )

(defn namespace-for
  ([^Symbol sym] (namespace-for *ns* sym))
  ([^Namespace inns, ^Symbol sym]
     (let [ns-sym (symbol (.ns sym))
           ns (.lookupAlias inns ns-sym )]
       (if (nil? ns)
         (Namespace/find ns-sym)
         ns))))

(defn- lookup-var* [sym intern-new?]
  (cond (not (nil? (namespace sym)))
        (let [ns (namespace-for sym)]
          (if (nil? ns)
            nil
            (let [name (symbol (name nil sym))]
              (if (and intern-new? (= ns *ns*))
                (.intern *ns* name)
                (.findInternedVar ns name)))))
        
        
        )
  )

(defn lookup-var
  ([sym intern-new?] (lookup-var sym intern-new? true))
  ([sym intern-new? register-macro?]
     (let [lookup-var* (fn [])])
     ))

(defn print-to-error-writer [message & args]
  (let [err clojure.core/*err*
        err-writer (if (instance? PrintWriter err)
                     err
                     (PrintWriter. err))]
    (.format err-writer (into-array args))))