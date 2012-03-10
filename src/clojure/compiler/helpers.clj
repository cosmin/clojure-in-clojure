(ns clojure.compiler.helpers
  (:use [clojure.utilities])
  (:import [clojure.lang IRecord])
  (:import [clojure.asm.commons Method]))

(def bind-root-method (Method/getMethod "void bindRoot(Object)"))
(def set-tag-method (Method/getMethod "void setTag(clojure.lang.Symbol)"))
(def set-meta-method (Method/getMethod "void setMeta(clojure.lang.IPersistentMap)"))
(def set-dynamic-method (Method/getMethod "clojure.lang.Var setDynamic(boolean)"))
(def symintern (Method/getMethod "clojure.lang.Symbol intern(String, String)"))
(def set-method (Method/getMethod "Object set(Object)"))
(def for-name-method (Method/getMethod "Class forName(String)"))
(def import-class-method (Method/getMethod "Class importClass(Class)"))
(def deref-method (Method/getMethod "Object deref()"))
(def invoke-no-arg-instance-member (Method/getMethod "Object invokeNoArgInstanceMember(Object,String)"))
(def set-instance-field-method (Method/getMethod "Object setInstanceField(Object,String,Object)"))
(def invoke-instance-method-method (Method/getMethod "Object invokeInstanceMethod(Object,String,Object[])"))
(def invoke-static-method-method (Method/getMethod "Object invokeStaticMethod(Class,String,Object[])"))
(def for-name-method (Method/getMethod "Class forName(String)"))
(def equiv-method (Method/getMethod "boolean equiv(Object, Object)"))
(def for-name-method (Method/getMethod "Class forName(String)"))
(def invoke-constructor-method (Method/getMethod "Object invokeConstructor(Class,Object[])"))
(def array-to-list-method (Method/getMethod "clojure.lang.ISeq arrayToList(Object[])"))
(def map-method (Method/getMethod "clojure.lang.IPersistentMap map(Object[])"))

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

(defmacro binding* [bindings & body]
  (let [not-if #(not (= :if %1))
        before-if (take-while not-if bindings)
        after-if (drop-while not-if bindings)
        condition (first (rest after-if))
        remaining (rest (rest after-if))
        new-vec (into [] before-if)
        new-vec (if condition (vec (concat new-vec remaining)) new-vec)]
    `(binding ~new-vec ~@body)))