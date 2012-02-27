(ns clojure.runtime
  (:import [clojure.lang Symbol Namespace])
  (:import [java.io PrintWriter])
  )

(defn err-print-writer []
  (let [err clojure.core/*err*]
    (if (instance? PrintWriter err)
      err
      (PrintWriter. err))))

(defn print-to-error-writer [message & args]
  (.format (err-print-writer) message (into-array args)))