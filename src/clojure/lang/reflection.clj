(ns clojure.lang.reflection
  (:use clojure.utilities)
  (:import [java.util ArrayList])
  (:import [clojure.lang Reflector])
  (:import [clojure.asm.commons GeneratorAdapter Method])
  (:import [java.lang.reflect Constructor Modifier]))


(defn- get-matching-params [method-name params args rets]
  (throw (RuntimeException. "get-matching-params not implemented")))

(defn- get-matching-method [methods method-name args]
  (if (> (.size methods) 1)
    (let [params (ArrayList.)
          rets (ArrayList.)]
      (doseq [i (range (.size methods))]
        (let [m (.get methods i)]
          (.add params (.getParameterTypes m))
          (.add rets (.getReturnType m))))
      (let [methodix (get-matching-params method-name params args rets)]
        (if (>= methodix 0) (.get methods methodix))))))

(defn get-method-with-name-and-args [methods method-name args]
  (if (empty? methods)
    nil
    (let [m (get-matching-method methods)]
      (if (and (not-nil? m)
               (not (Modifier/isPublic (.. m getDeclaringClass getModifiers))))
        (Reflector/getAsMethodOfPublicBase (.getDeclaringClass m) m)
        m))))

(defn invoke-static-method [method-name ms targetval argvals]
  (throw (RuntimeException. "invoke-static-method not implemented")))

(defn invoke-matching-method [method-name methods target args]
  (throw (RuntimeException. "invoke-matching-metho not implemented")))