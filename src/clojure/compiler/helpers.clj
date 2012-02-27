(ns clojure.compiler.helpers
  (:use [clojure.utilities])
  (:import [clojure.lang IRecord]))


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