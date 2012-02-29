(ns clojure.lang.reflection
  (:use clojure.utilities)
  (:import [java.util ArrayList])
  (:import [clojure.lang Reflector])
  (:import [clojure.asm.commons GeneratorAdapter Method])
  (:import [java.lang.reflect Constructor Modifier]))


(defn get-matching-params [method-name params args rets]
  (throw (RuntimeException. "get-matching-params not implemented")))

(defn get-matching-method [methods method-name args]
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

(defn box-arg [param-type arg]
  (let [unhandled (throw (IllegalArgumentException.
                          (str "Unexpected param type, expected: "
                               param-type ", given: " (.. arg getClass getName))))]
    (cond
     (not (.isPrimitive param-type)) (.cast param-type arg)
     (= Boolean/TYPE param-type) (boolean arg)
     (= Character/TYPE param-type) (char arg)
     (number? arg) (do
                     (let [n arg]
                       (condp = param-type
                         Integer/TYPE (.intValue n)
                         Float/TYPE (.floatValue n)
                         Double/TYPE (.doubleValue n)
                         Long/TYPE (.longValue n)
                         Short/TYPE (.shortValue n)
                         Byte/TYPE (.byteValue n)
                         (unhandled))))
     :else (unhandled))))

(defn box-args [params args]
  (when-not (= 0 (alength params))
    (into-array (for [i (range 0 (alength params))]
                  (let [arg (aget args i)
                        param-type (aget params i)]
                    (box-arg param-type arg))))))
