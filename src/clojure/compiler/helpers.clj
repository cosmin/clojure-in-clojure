(ns clojure.compiler.helpers
  (:use [clojure.utilities])
  (:use [clojure.runtime :only (lookup-var)])
  (:import [clojure.lang IRecord]))


(defn lookup-var-in-current-ns [sym]
  (let [v (lookup-var sym true)]
    (if (nil? v)
      (throw (RuntimeException. "Can't refer to qualified var that doesn't exist"))
      (if (not (= (namespace v) *ns*))
        (if (nil? (namespace sym))
          (.intern *ns* sym)
          (throw (RuntimeException. "Can't create defs outside of current ns")))))))

(defn tag-of [o]
  (let [tag (:tag (meta o))]
    (cond
     (symbol? tag) tag
     (string? tag) (symbol nil tag)
     :else nil)))

(defn represents-static? [sym]
  (not= \- (.charAt (name sym) 0)))

(defn eval-or-expression [context]
  (if (= :eval context) context :expression))

(defmacro visit-line-number []
  `(.visitLineNumber ~'gen ~'line (.mark ~'gen)))

(defmacro emit-clear-locals-if-return []
  `(if (= :return ~'context) (~'emit-clear-locals ~'*method*)))

(defmacro pop-if-statement []
  `(if (= :statement ~'context)
     (.pop ~'gen)))

(defn assignable-from? [from assignable]
  (. from isAssignableFrom assignable))

(defn record? [obj]
  (instance? IRecord obj))