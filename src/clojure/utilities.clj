(ns clojure.utilities)

(defn not-nil? [val]
  (not (nil? val)))

(defmacro cond-let [bindings & clauses]
  (let [binding (first bindings)]
    (when-let [[test expr & more] clauses]
      (if (= test :else)
        expr
        `(if-let [~binding ~test]
           ~expr
           (cond-let ~bindings ~@more))))))

(defn throw-runtime
  "Throws the supplied exception wrapped in a runtime exception,
  unless it is already a runtime exception"
  ([e]
     (if (instance? RuntimeException e)
       (throw e)
        (throw (RuntimeException. e)))))

(defn slice
  ([string start-idx]
     (slice string start-idx (.length string)))
  ([string start-idx end-idx]
     (let [len (.length string)
           positivize #(if (< %1 0) (+ len %1) %1)
           s (positivize start-idx)
           e (positivize end-idx)]
       (if (< s e)
         (.substring string s e)
         ""))))

(defn third [coll]
  (first (next (next coll))))

(defn fourth [coll]
  (first (next (next (next coll)))))
