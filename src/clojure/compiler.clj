(ns clojure.compiler
  (:refer-clojure :exclude [*file* *source-path* *compile-path* *compile-files*
                            munge macroexpand-1 macroexpand eval])
  (:use [clojure utilities runtime])
  (:use [clojure.compiler primitives helpers])
  (:use [clojure.lang reflection])
  (:require [clojure.lang.intrinsics :as intrinsics])
  (:import [clojure.lang ILookupSite ILookupThunk KeywordLookupSite IType])
  (:import [clojure.lang PersistentArrayMap PersistentHashSet PersistentVector PersistentList PersistentList$EmptyList])
  (:import [clojure.lang IPersistentList IPersistentMap IPersistentVector IPersistentSet])
  (:import [clojure.lang IFn AFunction IObj LazySeq ISeq RestFn AFn])
  (:import [clojure.lang Keyword Var Symbol Namespace])
  (:import [clojure.lang RT Numbers  Util Reflector Intrinsics])
  (:import [clojure.lang ArityException])
  (:import [clojure.asm Type Opcodes Label])
  (:import [clojure.asm.commons GeneratorAdapter Method])
  (:import [java.lang.reflect Constructor Modifier])
  (:import [java.util ArrayList LinkedList SortedMap TreeMap HashMap Set])
  (:import [java.util.regex Pattern]))

(declare analyze)
(declare emit-var)
(declare emit-var-value)
(declare register-local)

(declare emit-nil-expr)
(declare emit-clear-locals)
(declare host-expr-tag->class)

(declare parse-fn-expr)
(declare parse-def-expr)
(declare parse-let-expr)
(declare parse-recur-expr)
(declare parse-if-expr)
(declare parse-case-expr)
(declare parse-let-expr)
(declare parse-let-fn-expr)
(declare parse-body-expr)
(declare parse-constant-expr)
(declare parse-the-var-expr)
(declare parse-import-expr)
(declare parse-host-expr)
(declare parse-assign-expr)
(declare parse-new-instance-deftype-expr)
(declare parse-new-instance-reify-expr)
(declare parse-try-expr)
(declare parse-throw-expr)
(declare parse-monitor-enter-expr)
(declare parse-monitor-exit-expr)
(declare parse-new-expr)
(declare new-constant-expr)
(declare new-meta-expr)

(def char-map
  {\- "_",
   \: "_COLON_",
   \+ "_PLUS_",
   \> "_GT_",
   \< "_LT_",
   \= "_EQ_",
   \~ "_TILDE_",
   \! "_BANG_",
   \@ "_CIRCA_",
   \# "_SHARP_",
   \' "_SINGLEQUOTE_",
   \" "_DOUBLEQUOTE_",
   \% "_PERCENT_",
   \^ "_CARET_",
   \& "_AMPERSAND_",
   \* "_STAR_",
   \| "_BAR_",
   \{ "_LBRACE_",
   \} "_RBRACE_",
   \[ "_LBRACK_",
   \] "_RBRACK_",
   \/ "_SLASH_",
   \\ "_BSLASH_",
   \? "_QMARK_",
   \. "_DOT_"})

(defn munge [name]
  (apply str (map #(char-map % %) name)))

(defn is-field? [c instance sym]
  (when (represents-static? sym)
    (if c
      (= 0 (.size (Reflector/getMethods c 0 (munge (name sym)) true)))
      (if (and instance
               (.hasJavaClass instance)
               (.getJavaClass instance))
        (= 0 (.size (Reflector/getMethods (.getjavaclass instance) 0 (munge (name sym)) false)))
        ))))

(def compile-stub-prefix "compile__stub")
(def max-positional-arity 20)

(defmacro defasmtype [name klass]
  `(def ~name (Type/getType ~klass)))

(defasmtype object-type Object)
(defasmtype keyword-type Keyword)
(defasmtype var-type Var)
(defasmtype symbol-type Symbol)
(defasmtype ifn-type IFn)
(defasmtype afunction-type AFunction)
(defasmtype rt-type RT)
(defasmtype numbers-type Numbers)

(defasmtype class-type Class)
(defasmtype ns-type Namespace)
(defasmtype util-type Util)
(defasmtype reflector-type Reflector)
(defasmtype throwable-type Throwable)
(defasmtype boolean-object-type Boolean)
(defasmtype ipersistent-map-type IPersistentMap)
(defasmtype iobj-type IObj)

(def arg-types (make-array Type (+ max-positional-arity 2) 0))
(doseq [i (range (inc max-positional-arity))]
  (aset arg-types i (into-array Type (repeat i object-type))))

(let [max-arity-types (make-array Type (inc max-positional-arity))]
  (doseq [i (range max-positional-arity)]
    (aset max-arity-types i object-type))
  (aset max-arity-types max-positional-arity (Type/getType "[Ljava/lang/Object;"))
  (aset arg-types (inc max-positional-arity) max-arity-types))

(def ^:dynamic *local-env* nil)
(def ^:dynamic *loop-locals*)
(def ^:dynamic *loop-label*)
(def ^:dynamic *constants*)
(def ^:dynamic *constant-ids*)
(def ^:dynamic *keyword-callsites*)
(def ^:dynamic *protocol-callsites*)
(def ^:dynamic *var-callsites*)
(def ^:dynamic *keywords*)
(def ^:dynamic *vars*)
(def ^:dynamic *method* nil)
(def ^:dynamic *in-catch-finally* nil)
(def ^:dynamic *no-recur* nil)
(def ^:dynamic *loader*)

(def ^:dynamic *source* (intern 'clojure.core '*source-path* "NO_SOURCE_FILE"))
(def ^:dynamic *source-path* (intern 'clojure.core '*file* "NO_SOURCE_PATH"))
(def ^:dynamic *compile-path* (intern 'clojure.core '*compile-path* nil))
(def ^:dynamic *compile-files* (intern 'clojure.core '*compile-files* false))

(def ^:dynamic *line* 0)
(def ^:dynamic *line-before* 0)
(def ^:dynamic *line-after* 0)

(def ^:dynamic *next-local-num* 0)
(def ^:dynamic *ret-local-num* 0)
(def ^:dynamic *compile-stub-sym* nil)
(def ^:dynamic *compile-stub-class* nil)

(def ^:dynamic *clear-path* nil)
(def ^:dynamic *clear-root* nil)
(def ^:dynamic *clear-sites* nil)

(defn meta-add-source-line-doc [mm docstring]
  (let [source-path (if-not *source-path* "NO_SOURCE_FILE" *source-path*)
        mm (assoc mm :line *line* :file source-path)]
    (if docstring
      (assoc mm :doc docstring)
      mm)))

(def ^:private const-prefix "const__")

(defn- constant-type [objx id]
  (let [constants (:constants objx)
        o (nth constants id)
        c (class o)]
    (when (and c (Modifier/isPublic (.getModifiers c)))
      (cond
       (assignable-from? LazySeq c) (Type/getType ISeq)
       (= Keyword c) (Type/getType Keyword)
       (assignable-from? RestFn c) (Type/getType RestFn)
       (assignable-from? AFn c) (Type/getType AFn)
       (= Var c) (Type/getType Var)
       (= String c) (Type/getType String))
      object-type)))

(defn- constant-name [id]
  (str const-prefix id))

(defn- emit-constant [objx gen id]
  (.getStatic gen (:objtype objx) (constant-name id) (constant-type id)))

(defn- emit-keyword [objx gen ^Keyword k]
  (let [i (get (:keywords objx) k)]
    (emit-constant objx gen i)))

(defn- prim-class [^Symbol sym]
  (when sym
    (condp = (name sym)
      "int" Integer/TYPE
      "long" Long/TYPE
      "float" Float/TYPE
      "double" Double/TYPE
      "char" Character/TYPE
      "short" Short/TYPE
      "byte" Byte/TYPE
      "boolean" Boolean/TYPE
      "void" Void/TYPE
      nil)))

(defn- class-char [x]
  (let [c (cond (class? x) x
                (symbol? x) (prim-class x))]
    (cond
     (or (nil? c) (not (.isPrimitive c))) \O
     (= Long/TYPE c) \L
     (= Double/TYPE c) \D
     :else (throw (IllegalArgumentException.
                   "Only long and double primitives are supported")))))

(defn tag-of [o]
  (let [tag (:tag (meta o))]
    (cond
     (symbol? tag) tag
     (string? tag) (symbol nil tag)
     :else nil)))

(defn- prim-interface [arglist]
  (let [sb (StringBuilder.)]
    (doseq [i (range (count arglist))]
      (.append sb (class-char (tag-of (nth arglist i)))))
    (.append sb (class-char (tag-of arglist)))
    (let [ret (.toString sb)
          prim? (or (.contains ret "L") (.contains ret "D"))]
      (cond (and prim? (> (count arglist) 4))
            (throw (IllegalArgumentException.
                    "fns taking primitives support only 4 or fewer args"))

            prim?
            (str "clojure.lang.IFn$" ret)

            :else
            nil))))

(defn namespace-for
  ([^Symbol sym] (namespace-for *ns* sym))
  ([^Namespace inns, ^Symbol sym]
     (let [ns-sym (symbol (namespace sym))
           ns (.lookupAlias inns ns-sym )]
       (if (nil? ns)
         (Namespace/find ns-sym)
         ns))))

(defn- lookup-var* [sym intern-new?]
  (cond (namespace sym)
        (let [ns (namespace-for sym)]
          (if (nil? ns)
            nil
            (let [name (symbol nil (name sym))]
              (if (and intern-new? (= ns *ns*))
                (.intern *ns* name)
                (.findInternedVar ns name)))))

        (= sym 'ns) #'clojure.core/ns
        (= sym 'in-ns) #'clojure.core/in-ns
        :else
        (let [o (.getMapping *ns* sym)]
          (cond (nil? o)
                (when intern-new?
                  (.intern *ns* (symbol (name sym))))

                (var? o) o
                :else (throw (RuntimeException. (str "Expecting var, but "
                                                     sym
                                                     " is mapped to "
                                                     o)))))))

(defn- register-constant [o]
  (if-not (bound? #'*constants*)
    -1
    (let [i (.get *constant-ids* o)]
      (if i
        i
        (do
          (var-set *constants* (conj *constants* o))
          (.put *constant-ids* o (count *constants*))
          (count *constants*))))))

(defn register-var [v]
  (if (bound? #'*vars*)
    (let [id (get *vars* v)]
      (if (nil? id)
        (var-set *vars* (assoc *vars* v (register-constant v)))))))

(defn lookup-var
  ([sym intern-new?] (lookup-var sym intern-new? true))
  ([sym intern-new? register-macro?]
     (let [var (lookup-var* sym intern-new?)]
       (when (and var (or (not (.isMacro var)) register-macro?))
         (register-var var))
       var)))

(defn lookup-var-in-current-ns [sym]
  (let [v (lookup-var sym true)]
    (if (nil? v)
      (throw (RuntimeException. "Can't refer to qualified var that doesn't exist"))
      (if (not (= (namespace v) *ns*))
        (if (nil? (namespace sym))
          (.intern *ns* sym)
          (throw (RuntimeException. "Can't create defs outside of current ns")))))))

(defprotocol Expr
  (evaluate [this])
  (emit [this context objx ^GeneratorAdapter gen])
  (has-java-class? [this])
  (^Class get-java-class [this]))

(defprotocol AssignableExpr
  (eval-assign [this val])
  (emit-assign [this context objx gen val]))

(defprotocol LiteralExpr
  (value [this]))

(defprotocol MaybePrimitiveExpr
  (can-emit-primitive [this])
  (emit-unboxed [this context, ^clojure.compiler.ObjExpr objx,^GeneratorAdapter gen]))

(defprotocol MaybeIntrinsicPredicate
  (can-emit-intrinsic-predicate [this])
  (emit-intrinsic-predicate [this context objx gen false-label]))


(declare FnExpr)

(defrecord DefExpr [^Var var, init, meta,
                    init-provided?, dynamic?,
                    ^String source, ^long line]
  Expr
  (evaluate [this]
    (when init-provided?
      (.bindRoot var (evaluate init)))
    (when meta
      (.setMeta (evaluate meta)))
    (.setDynamic var dynamic?))
  (emit [this context objx gen]
    (do
      (.emitVar objx gen var)
      (if dynamic?
        (do
          (.push gen dynamic?)
          (.invokeVirtual gen var-type set-dynamic-method)))
      (when meta
        (.dup gen)
        (emit meta :expression objx gen)
        (.checkCast gen ipersistent-map-type)
        (.invokeVirtual gen var-type set-meta-method))
      (when init-provided?
        (.dup gen)
        (if (instance? FnExpr init)
          (.emitForDefn init objx gen)
          (emit init :expression objx gen))
        (.invokeVirtual gen var-type bind-root-method))
      (pop-if-statement)))
  (has-java-class? [init] true)
  (get-java-class [init] Var))

(defn parse-def-expr
  ([context form]
     (if (and (= 4 (count form)) (string? (third form)))
       (parse-def-expr
         context
         (list (first form) (second form) (fourth form))
         (third form))
       (parse-def-expr context form nil)))
  ([context form docstring]
     (cond
      (> (count form) 3)
      (throw (RuntimeException. "Too many arguments to def"))

      (< (count form) 2)
      (throw (RuntimeException. "Too few arguments to def"))

      (not (symbol? (second form)))
      (throw (RuntimeException. "First argument to def must be a Symbol")))
     (let [sym (second form)
           v (lookup-var-in-current-ns sym)
           mm (meta sym)
           dynamic? (:dynamic mm)]
       (when dynamic?
         (.setDynamic v))
       (if (and (.startsWith (name sym) "*")
                (.endsWith (name sym) "*")
                (> 1 (.length (name sym))))
         (print-to-error-writer
          (str "Warning: %1$s not declared dynamic "
               "and thus is not dynamically rebindable, "
               "but its name suggests otherwise. "
               "Please either indicate ^:dynamic %1$s "
               "or change the name. (%2$s:%3$d)\n")
          sym *source-path*, *line*))
       (when (:arglists mm)
         (let [vm (meta v)]
           (.setMeta v (assoc vm :arglists (second (:arglists mm))))))
       (let [mm (meta-add-source-line-doc mm docstring)
             mcontext (eval-or-expression context)
             meta (if (= 0 (count mm)) nil (analyze mcontext mm))]
         (map->DefExpr {:source *source*
                        :line *line*
                        :var v
                        :init (analyze mcontext (third form))
                        :meta meta
                        :init-provided? (= 3 (count form))
                        :dynamic? dynamic?})))))

(defrecord AssignExpr [^clojure.compiler.AssignableExpr target,
                       ^clojure.compiler.Expr val]

  Expr
  (evaluate [this] (eval-assign target val))
  (emit [this context objx gen] (emit-assign target context objx gen val))
  (has-java-class? [this] (has-java-class? val))
  (get-java-class [this] (get-java-class val)))

(defn parse-assign-expr [context form]
  (if  (not= 3 (count form))
    (throw (IllegalArgumentException. "Malformed assignment, expecting (set! target val)"))
    (let [target (analyze :expression (second form))]
      (if (not (satisfies? AssignableExpr target))
        (throw (IllegalArgumentException. "Invalid assignment target"))
        (map->AssignExpr {:target target
                          :val (analyze :expression (third form))})))))


(defrecord VarExpr [^Var var, tag]
  Expr
  (evaluate [this] (.deref var))
  (emit [this context objx gen]
    (emit-var-value objx gen var)
    (when (= :statement context)
      (.pop gen)))
  (has-java-class? [this] (not-nil? tag))
  (get-java-class [this] (host-expr-tag->class tag))

  AssignableExpr
  (eval-assign [this val] (var-set var (evaluate val)))
  (emit-assign [this context objx gen val]
    (do
      (emit-var objx var)
      (emit val :expression objx gen)
      (.invokeVirtual gen var-type set-method)
      (pop-if-statement))))

(defrecord TheVarExpr [^Var var]
  Expr
  (evaluate [this] var)
  (emit [this context objx gen]
    (emit-var objx gen var)
    (when (= :statement context)
      (.pop gen)))
  (has-java-class? [this] true)
  (get-java-class [this] Var))


(defn parse-the-var-expr [context form]
  (let [sym (second form)
        v (lookup-var sym false)]
    (if v
      (->TheVarExpr v)
      (throw (RuntimeException. (str "Unable to resolve var: " sym
                                     " in this context"))))))


(defrecord KeywordExpr [^Keyword k]
  LiteralExpr
  (value [this] k)

  Expr
  (evaluate [this] k)
  (emit [this context objx gen]
    (emit-keyword objx gen k)
    (when (= :statement context)
      (.pop gen)))
  (has-java-class? [this] true)
  (get-java-class [this] Keyword))

(defn new-keyword-expr [k]
  (->KeywordExpr k))

(defrecord ImportExpr [^String c]
  Expr
  (evaluate [this]
    (do
      (.importClass *ns* (RT/classForName c))
      nil))

  (emit [this context objx gen]
    (doto gen
      (.genStatic rt-type "CURRENT_NS" var-type)
      (.invokeVirtual var-type deref-method)
      (.checkCast ns-type)
      (.push c)
      (.invokeStatic class-type for-name-method)
      (.invokeVirtual ns-type import-class-method))
    (pop-if-statement))

  (has-java-class? [this] false)
  (get-java-class [this] (throw (IllegalArgumentException. "ImportExpr has no Java class"))))

(defn parse-import-expr [context form]
  (->ImportExpr (second form)))

(defn emit-box-return [objx, ^GeneratorAdapter gen, ^Class return-type]
  (when (.isPrimitive return-type)
    (condp = return-type
      Boolean/TYPE
      (do
        (let [false-label (.newLabel gen)
              end-label (.newLabel gen)]
          (doto gen
            (.ifZCmp GeneratorAdapter/EQ false-label)
            (.getStatic boolean-object-type, "TRUE", boolean-object-type)
            (.goTo end-label)
            (.mark false-label)
            (.getStatic boolean-object-type, "FALSE", boolean-object-type)
            (.mark end-label))))

      Void/TYPE (emit-nil-expr :expression objx gen)
      Character/TYPE (.invokeStatic gen char-type char-value-of-method)
      Integer/TYPE (.invokeStatic gen integer-type int-value-of-method)
      Float/TYPE (.invokeStatic gen float-type float-value-of-method)
      Double/TYPE (.invokeStatic gen double-type double-value-method)
      Long/TYPE (.invokeStatic gen number-type (Method/getMethod "Number num(long)"))
      Byte/TYPE (.invokeStatic gen byte-type byte-value-of-method)
      Short/TYPE (.invokeStatic gen short-type short-value-of-method))))

(defn- maybe-primitive-type [e]
  (try
    (when (and (satisfies? MaybePrimitiveExpr e)
             (has-java-class? e)
             (can-emit-primitive e))
      (let [c (get-java-class e)]
        (when (primitive? c) c)))
    (catch Exception ex
      (throw-runtime ex))))

(defn- get-primitive-cast-method [param-type]
  (if clojure.core/*unchecked-math*
    (condp = param-type
      Integer/TYPE (Method/getMethod "int uncheckedIntCast(Object)")
      Float/TYPE (Method/getMethod "float uncheckedFloatCast(Object)")
      Double/TYPE (Method/getMethod "double uncheckedDoubleCast(Object)")
      Long/TYPE (Method/getMethod "long uncheckedLongCast(Object)")
      Byte/TYPE (Method/getMethod "byte uncheckedByteCast(Object)")
      Short/TYPE (Method/getMethod "short uncheckedShortCast(Object)"))
    (condp = param-type
      Integer/TYPE (Method/getMethod "int intCast(Object)")
      Float/TYPE (Method/getMethod "float floatCast(Object)")
      Double/TYPE (Method/getMethod "double doubleCast(Object)")
      Long/TYPE (Method/getMethod "long longCast(Object)")
      Byte/TYPE (Method/getMethod "byte byteCast(Object)")
      Short/TYPE (Method/getMethod "short shortCast(Object)"))))

(defn emit-unbox-arg [objx, ^GeneratorAdapter gen, ^Class param-type]
  (if (.isPrimitive param-type)
    (condp = param-type
      Boolean/TYPE (doto gen
                     (.checkCast boolean-type)
                     (.invokeVirtual gen boolean-type boolean-value-method))

      Character/TYPE (doto gen
                       (.checkCast char-type)
                       (.invokeVirtual char-type char-value-method))
      (do
        (.checkCast number-type)
        (let [m (get-primitive-cast-method param-type)]
          (.invokeStatic gen rt-type m))))
    (.checkCast gen (Type/getType param-type))))

(defn emit-args-as-array [args objx ^GeneratorAdapter gen]
  (.push gen (count args))
  (.newArray gen object-type)
  (doseq [i (range count)]
    (.dup gen)
    (.push gen i)
    (emit (nth args i) :expression objx gen)
    (.arrayStore gen object-type)))

(defn emit-typed-args [objx, ^GeneratorAdapter gen, parameter-types, args]
  (doseq [i (range (alength parameter-types))]
    (let [e (nth args i)]
      (try
        (let [primc (maybe-primitive-type e)]
          (cond
           (= primc (aget parameter-types i))
           (emit-unboxed e :expression objx gen)

           (and (= primc Integer/TYPE) (= Long/TYPE (aget parameter-types i)))
           (do
             (emit-unboxed e :expression objx gen)
             (.visitInsn gen Opcodes/I2L))

           (and (= Long/TYPE primc) (= Integer/TYPE (aget parameter-types i)))
           (do
             (emit-unboxed e :expression objx gen)
             (if clojure.core/*unchecked-math*
               (.invokeStatic gen
                              rt-type
                              (Method/getMethod "int uncheckedIntCast(long)"))
               (.invokeStatic gen
                              rt-type
                              (Method/getMethod "int intCast(long)"))))

           (and (= Float/TYPE primc) (= Double/TYPE (aget parameter-types i)))
           (do
             (emit-unboxed e :expression objx gen)
             (.visitInsn gen Opcodes/F2D))

           (and (= Double/TYPE primc) (= Float/TYPE (aget parameter-types i)))
           (do
             (emit-unboxed e :expression objx gen)
             (.visitInsn gen Opcodes/D2F))

           :else
           (do
             (emit e :expression objx gen)
             (emit-unbox-arg objx gen (aget parameter-types i)))))
        (catch Exception e1
          (.printStackTrace e1 (err-print-writer)))))))

(defrecord ThrowExpr [exc-expr]
  Expr
  (has-java-class? [this] false)
  (get-java-class [this] (throw (IllegalArgumentException. "Has no Java class")))
  (evaluate [this] (throw (RuntimeException. "Can't eval throw")))
  (emit [this context objx gen]
    (emit exc-expr :expression objx gen)
    (.checkCast gen throwable-type)
    (.throwException gen)))

(defn parse-throw-expr [context form]
  (if (= :eval context)
    (analyze context (list (list 'fn* [] form)))
    (->ThrowExpr (analyze :expression (second form)))))

(defn maybe-class [form, string-ok?]
  (cond
   (class? form)
   form

   (symbol? form)
   (let [sym form]
     (when-not (namespace sym) ; if ns-qualified can't be classname
       (cond
        (= sym *compile-stub-sym*)
        *compile-stub-class*

        (or (> (.indexOf (name sym) ".") 0)
            (= \[ (.charAt (name sym) 0)))
        (RT/classForName (name sym))

        :else
        (let [o (.getMapping *ns* sym)]
          (if (class? o)
            o
            (try
              (RT/classForName (name sym))
              (catch Exception e
                nil)))))))

   (and string-ok? (string? form))
   (RT/classForName form)

   :else
   nil))

(defn tag-to-class [tag]
  (let [c (maybe-class tag true)
        array-class (when (symbol? tag)
                      (let [sym tag]
                        ; if ns-qualified can't be classname
                        (when-not (namespace sym)
                          (condp = (name sym)
                            "objects" object-array-class
                            "ints" int-array-class
                            "longs" long-array-class
                            "floats" float-array-class
                            "doubles" double-array-class
                            "chars" char-array-class
                            "shorts" short-array-class
                            "bytes" byte-array-class
                            "booleans" boolean-array-class))))]
    (if array-class
      array-class
      (if c
        c
        (throw (IllegalArgumentException.
                (str "Unable to resolve classname: " tag)))))))

(defn destub-class-name [class-name]
  (if (.startsWith class-name compile-stub-prefix)
    (.substring class-name (inc (.length compile-stub-prefix)))
    class-name))

(defrecord NewExpr [args ctor c]
  Expr
  (evaluate [this]
    (let [argvals (into-array (map evaluate args))]
      (if ctor
        (try
          (.newInstance ctor (box-args (.getParameterTypes ctor) argvals))
          (catch Exception e
            (throw-runtime e)))
        (Reflector/invokeConstructor c argvals))))
  (emit [this context objx gen]
    (if ctor
      (let [type (Type/getType c)]
        (.newInstance gen type)
        (.dup gen)
        (emit-typed-args objx gen (.getParameterTypes ctor) args)
        (emit-clear-locals-if-return)
        (.invokeConstructor gen type (Method. "<init>"
                                              (Type/getConstructorDescriptor ctor))))
      (do
        (.push gen (destub-class-name (.getName c)))
        (.invokeStatic gen class-type for-name-method)
        (emit-args-as-array args objx gen)
        (emit-clear-locals-if-return)
        (.invokeStatic gen reflector-type invoke-constructor-method)))
    (if (= :statement context)
      (.pop gen)))
  (has-java-class? [this] true)
  (get-java-class [this] c))

(defn new-new-expr [c args line]
  (let [allctors (.getConstructors c)
        ctors (ArrayList.)
        params (ArrayList.)
        rets (ArrayList.)]
    (doseq [ctor allctors]
      (when (= (count args) (alength (.getParameterTypes ctor)))
        (.add ctors ctor)
        (.add params (.getParameterTypes ctor))
        (.add rets c)))
    (when (.isEmpty ctors)
      (throw (IllegalArgumentException. (str "No matching ctor found for " c))))
    (let [ctoridx (if (> (.size ctors) 1)
                    (get-matching-params (.getName c) params args rets)
                    0)]
      (let [ctor (if (>= ctoridx 0) (.get ctors ctoridx))]
        (when-not ctor
          (print-to-error-writer "Reflection warning, %s:%d - call to %s ctor can't be resolved.\n" *source-path* line (.getName c)))
        (map->NewExpr {:args args :c c :ctor ctor})))))

(defn parse-new-expr [context form]
  (when (< (count form) 2)
    (throw (RuntimeException. "wrong number of arguments, expecting: (new Classname args...)")))
  (let [c (maybe-class (second form) false)]
    (when-not c
      (throw (IllegalArgumentException. (str "Unable to resolve classname: "
                                             (second form)))))
    (let [args (into [] (map (partial analyze (eval-or-expression context))
                             (next (next form))))]
      (new-new-expr c args *line*))))


(defn- maybe-java-class [exprs]
  (let [without-throw (filter #(not (instance? ThrowExpr %)) exprs)
        with-java-class (filter #(has-java-class? %1) without-throw)
        first-match (first with-java-class)
        second-match (second with-java-class)]
    (when first-match
      (when-not second-match
        first-match))))


(defrecord StaticFieldExpr [field-name c field tag line]
  Expr
  (evaluate [this] (Reflector/getStaticField c field-name))
  (emit [this context objx gen]
    (visit-line-number)
    (.getStatic gen (Type/getType c) field-name (Type/getType (.getType field)))
    (emit-box-return objx gen (.getType field))
    (when (= :statement context)
      (.pop gen)))
  (has-java-class? [this] true)
  (get-java-class [this] (if tag (tag-to-class tag) (.getType field)))

  MaybePrimitiveExpr
  (can-emit-primitive [this] (primitive? (.getType field)))
  (emit-unboxed [this context objx gen]
    (visit-line-number)
    (.getStatic gen (Type/getType c) field-name (Type/getType (.getType field))))


  AssignableExpr
  (eval-assign [this val] (Reflector/setStaticField c field-name (evaluate val)))
  (emit-assign [this context objx gen val]
    (visit-line-number)
    (emit val :expression objx gen)
    (.dup gen)
    (emit-unbox-arg objx gen (.getType field))
    (.putStatic gen (Type/getType c) field-name (Type/getType (.getType field)))
    (when (= :statement context)
      (.pop gen))))

(defn new-static-field-expr [line c field-name tag]
  (try
    (let [field (.getField c field-name)]
      (map->StaticFieldExpr {:field-name field-name
                             :line line
                             :c c
                             :field field
                             :tag tag}))
    (catch NoSuchFieldException e
      (throw-runtime e))))


(defrecord InstanceFieldExpr [target target-class field field-name line tag]
  Expr
  (evaluate [this]
    (Reflector/invokeNoArgInstanceMember (evaluate target) field-name))
  (emit [this context objx gen]
    (visit-line-number)
    (if (and target-class field)
      (do (emit target :expression objx gen)
          (doto gen
            (.checkCast (Type/getType target-class))
            (.getField (Type/getType target-class)
                       field-name
                       (Type/getType (.getType field))))
          (emit-box-return objx gen (.getType field))
          (when (= :statement context)
            (.pop gen)))
      (do (emit target :expression objx gen)
          (doto gen
            (.push field-name)
            (.invokeStatic reflector-type invoke-no-arg-instance-member))
          (when (= :statement context)
            (.pop gen)))))
  (has-java-class? [this] (or field tag))
  (get-java-class [this]
    (if tag
      (tag-to-class tag)
      (.getType field)))

  MaybePrimitiveExpr
  (can-emit-primitive [this]
    (and target-class
         field
         (primitive? (.getType field))))
  (emit-unboxed [this context objx gen]
    (visit-line-number)
    (if (and target-class field)
      (do (emit target :expression objx gen)
          (doto gen
            (.checkCast (Type/getType target-class))
            (.getField (Type/getType target-class)
                       field-name
                       (Type/getType (.getType field)))))
      (throw (UnsupportedOperationException. "Unboxed emit of unknown member"))))

  AssignableExpr
  (eval-assign [this val]
    (Reflector/setInstanceField (evaluate target) field-name (evaluate val)))
  (emit-assign [this context objx gen val]
    (visit-line-number)
    (if (and target-class field)
      (do (emit target :expression objx gen)
          (.checkCast gen (Type/getType target-class))
          (emit val :expression objx gen)
          (.dupX1 gen)
          (emit-unbox-arg objx gen (.getType field))
          (.putField gen
                     (Type/getType target-class)
                     field-name
                     (Type/getType (.getType field))))
      (do (emit target :expression objx gen)
          (.push gen field-name)
          (emit val :expression objx gen)
          (.invokeStatic gen reflector-type set-instance-field-method)
          )
      )
    )

  )

(defn new-instance-field-expr [line target field-name tag]
  (let [target-class (if (has-java-class? target) (get-java-class target))
        field (if target-class (Reflector/getField target-class field-name false))]
    (if (and (nil? field) clojure.core/*warn-on-reflection*)
      (print-to-error-writer "Reflection warning, %s:%d - reference to field %s can't be resolved.\n" *source-path* line field-name))
    (map->InstanceFieldExpr {:target target
                             :target-class target-class
                             :field field
                             :field-name field-name
                             :line line
                             :tag tag})))


(defrecord StaticMethodExpr [c method-name args source line method tag]
  Expr
  (evaluate [this]
    (try
      (let [argvals (make-array Object (count args))]
        (doseq [i (range (count args))]
          (aset argvals (evaluate (nth args i))))
        (if method
          (let [ms (LinkedList.)]
            (.add ms method)
            (invoke-matching-method method-name ms nil argvals))
          (invoke-static-method c method-name argvals)))
      (catch Throwable e
        (if (instance? clojure.lang.Compiler$CompilerException e)
          (throw e)
          (throw (clojure.lang.Compiler$CompilerException. source line e))))))
  (emit [this context objx gen]
    (visit-line-number)
    (if method
      (do
        (emit-typed-args objx gen (.getParameterTypes method) args)
        (emit-clear-locals-if-return)
        (let [type (Type/getType c)
              m (Method. method-name
                         (Type/getReturnType method)
                         (Type/getArgumentTypes method))]
          (.invokeStatic gen type m))
        (let [ret-class (.getReturnType method)]
          (if (= :statement context)
            (cond (or (= Long/TYPE ret-class) (= Double/TYPE ret-class))
                  (.pop2 gen)

                  (not= Void/TYPE ret-class)
                  (.pop gen))
            (emit-box-return objx gen (.getReturnType method)))))
      (do
        (doto gen
          (.push (.getName c))
          (.invokeStatic class-type for-name-method)
          (.push method-name))
        (emit-args-as-array args objx gen)
        (emit-clear-locals-if-return)
        (.invokeStatic gen reflector-type invoke-static-method-method)
        (pop-if-statement))))
  (has-java-class? [this] (or method tag))
  (get-java-class [this]
    (if tag
      (tag-to-class tag)
      (.getReturnType method)))

  MaybeIntrinsicPredicate
  (can-emit-intrinsic-predicate [this]
    (and method (get intrinsics/preds (.toString method))))

  (emit-intrinsic-predicate [this context objx gen false-label]
    (visit-line-number)
    (if-not method
      (throw (UnsupportedOperationException. "Unboxed emit of unknown member"))
      (do
        (emit-typed-args objx gen (.getParameterTypes method) args)
        (emit-clear-locals-if-return)
        (let [pred-ops (get intrinsics/preds (.toString method))]
          (doseq [i (range (dec (alength pred-ops)))]
            (.visitInsn gen (aget pred-ops i)))
          (.visitJumpInsn gen (aget pred-ops (dec (alength pred-ops))) false-label)))))

  MaybePrimitiveExpr
  (can-emit-primitive [this]
    (and method (primitive? (.getReturnType method))))
  (emit-unboxed [this context objx gen]
    (visit-line-number)
    (if-not method
      (throw (UnsupportedOperationException. "Unboxed emit of unknown member"))
      (do
        (emit-typed-args objx gen (.getParameterTypes method) args)
        (emit-clear-locals-if-return)
        (let [ops (get intrinsics/preds (.toString method))]
          (if ops
            (if (instance? object-array-class ops)
              (doseq [op ops]
                (.visitInsn gen op))
              (.visitInsn gen ops))
            (let [type (Type/getType c)
                  m (Method. method-name
                             (Type/getReturnType method)
                             (Type/getArgumentTypes method))]
              (.invokeStatic gen type m)))))))

  )

(defn new-static-method-expr [source line tag c method-name args]
  (let [methods (Reflector/getMethods c (count args) method-name true)]
    (if (.isEmpty methods)
      (throw (IllegalArgumentException. (str "No matching method: " method-name)))
      (let [method (get-method-with-name-and-args methods method-name args)]
        (if (and (nil? method) clojure.core/*warn-on-reflection*)
          (print-to-error-writer "Reflection warning, %s:%d - call to %s can't be resolved.\n" *source-path* line method-name))
        (map->StaticMethodExpr {:c c
                                :method-name method-name
                                :args args
                                :source source
                                :line line
                                :method method
                                :tag tag})))))

(defrecord InstanceMethodExpr [target method-name args source line tag method]
  Expr
  (evaluate [this]
    (try
      (let [targetval (evaluate target)
            argvals (make-array Object (count args))]
        (doseq [i (range (count args))]
          (aset argvals i (evaluate (nth args i))))
        (when method
          (let [ms (LinkedList.)]
            (.add ms method)
            (invoke-matching-method method-name ms targetval argvals)))
        (Reflector/invokeInstanceMethod targetval method-name argvals))
      (catch Throwable e
        (if (instance? clojure.lang.Compiler$CompilerException e)
          (throw e)
          (throw (clojure.lang.Compiler$CompilerException. source line e))))))
  (emit [this context objx gen]
    (.visitLineNumber line (.mark gen))
    (when method
      (let [type (Type/getType (.getDeclaringClass method))]
        (emit target :expression objx gen)
        (.checkCast gen type)
        (emit-typed-args objx gen (.getParameterTypes method) args)
        (emit-clear-locals-if-return)
        (let [m (Method. method-name (Type/getReturnType method) (Type/getArgumentTypes method))]
          (if (.. method getDeclaringClass isInterface)
            (.invokeInterface gen type m)
            (.invokeVirtual gen type m)))
        (emit-box-return objx gen (.getReturnType method)))))
  (has-java-class? [this] (not (and (nil? method) (nil? tag))))
  (get-java-class [this]
    (if tag
      (tag-to-class tag)
      (.getReturnType method)))

  MaybePrimitiveExpr
  (can-emit-primitive [this]
    (and method (primitive? (.getReturnType method))))
  (emit-unboxed [this context objx gen]
    (visit-line-number)
    (if-not method
      (throw (UnsupportedOperationException. "Unboxed emit of unknown member"))
      (let [type (Type/getType (.getDeclaringClass method))]
        (emit target :expression objx gen)
        (.checkCast gen type)
        (emit-typed-args objx gen (.getParameterTypes method) args)
        (emit-clear-locals-if-return)
        (let [m (Method. method-name (Type/getReturnType method) (Type/getArgumentTypes method))]
          (if (.. method getDeclaringClass isInterface)
            (.invokeInterface gen type m)
            (.invokeVirtual gen type m)))))))

(defn new-instance-method-expr [source line tag target method-name args]
  (let [method (when (and (has-java-class? target) (get-java-class target))
                 (let [methods (Reflector/getMethods (get-java-class target)
                                                     (count args)
                                                     method-name
                                                     false)]
                   (get-method-with-name-and-args methods method-name args)))]
    (when (and (nil? method) clojure.core/*warn-on-reflection*)
      (print-to-error-writer "Reflection warning, %s:%d - call to %s can't be resolved.\n" *source-path* line method-name))
    (map->InstanceMethodExpr {:target target
                              :method-name method-name
                              :args args
                              :source source
                              :line line
                              :tag tag
                              :method method})))

(defn host-expr-parser [context form]
  (if (< (count form) 3)
    (throw (IllegalArgumentException. "malformed member expression, expecting (. target member ...)")))
  (let [c (maybe-class (second form false))
        icontext (eval-or-expression context)
        instance (when-not c (analyze icontext (second form)))
        third-form (third form)
        maybe-field (and (= 3 (count form)) (symbol? third-form))
        field? (when maybe-field (is-field? c instance third-form))]
    (if field?
      (let [sym (if (represents-static? third-form)
                  (symbol (.substring (name third-form) 1))
                  third-form)
            tag (tag-of form)
            field-name (munge (name sym))]
        (if c
          (new-static-field-expr *line* c field-name tag)
          (new-instance-field-expr *line* instance field-name tag)))
      (let [call (if (seq? third-form) third-form (next (next form)))]
        (when-not (symbol? (first call))
          (throw (IllegalArgumentException. "Malformed member expression")))
        (let [sym (first call)
              tag (tag-of form)
              args (into [] (map #(analyze (eval-or-expression context) %1)))
              field-name (munge (name sym))]
          (if c
            (new-static-method-expr *source* *line* tag c field-name args)
            (new-instance-method-expr *source* *line* tag instance field-name args)))))))

(defrecord UnresolvedVarExpr [symbol]
  Expr
  (has-java-class? [this] false)
  (get-java-class [this] (throw (IllegalArgumentException. "UnresolvedVarExpr has no Java class")))
  (emit [this context objx gen]
    )
  (evaluate [this]
    (throw (IllegalArgumentException. "UnresolvedVarExpr cannot be evalled"))))

(defrecord NumberExpr [^Number n, id]
  LiteralExpr
  (value [this] n)

  Expr
  (evaluate [this] n)
  (emit [this context objx gen]
    (when-not (= :statement context)
      (emit-constant objx gen id)))
  (has-java-class? [this] true)
  (get-java-class [this]
    (cond
     (instance? Integer n) Long/TYPE
     (instance? Double n) Double/TYPE
     (instance? Long n) Long/TYPE
     :else (throw (IllegalStateException. (str "Unsupported Number type: "
                                               (.getName (class n)))))))

  MaybePrimitiveExpr
  (can-emit-primitive [this] true)
  (emit-unboxed [this context objx gen]
    (cond
     (instance? Integer n) (.push gen (.longValue n))
     (instance? Double n) (.push gen (.doubleValue n))
     (instance? Long n) (.push gen (.longValue n)))))


(defn- register-keyword-callsite [kw]
  (if-not (bound? #'*keyword-callsites*)
    (throw (IllegalAccessError. "KEYWORD_CALLSITES is not bound"))
    (do
      (var-set *keyword-callsites* (conj *keyword-callsites* kw))
      (dec (count *keyword-callsites*)))))

(declare register-protocol-callsite)

(defn- site-name [n]
  (str "__site__" n))

(defn- site-name-static [n]
  (str (site-name n) "__"))

(defn- thunk-name [n]
  (str "__thunk__" n))

(defn- cached-class-name [n]
  (str "__cached_class__" n))

(defn- cached-var-name [n]
  (str "__cached_var__" n))

(defn- cached-proto-fn-name [n]
  (str "__cached_proto_fn__" n))

(defn- cached-proto-impl-name [n]
  (str "__cached_proto_impl__" n))

(defn- var-callsite-name [n]
  (str "__var__callsite__" n))

(defn- thunk-name-static [n]
  (str (thunk-name n) "__"))

(def ilookup-site-type (Type/getType ILookupSite))
(def ilookup-thunk-type (Type/getType ILookupThunk))
(def keyword-lookupsite-type (Type/getType KeywordLookupSite))

(defn new-number-expr [n]
  (map->NumberExpr {:n n
                    :id (register-constant n)}))

(defn parse-number-expr [^Number form]
  (if (or (instance? Integer form)
          (instance? Double form)
          (instance? Long form))
    (new-number-expr form)
    (new-constant-expr form)))

(def nil-expr
  (reify
    LiteralExpr
    (value [this] nil)

    Expr
    (evaluate [this] nil)
    (emit [this context objx gen]
      (.visitInsn gen Opcodes/ACONST_NULL)
      (pop-if-statement))
    (has-java-class? [this] true)
    (get-java-class [this] nil)))

(defrecord BooleanExpr [val]
  LiteralExpr
  (value [this] (if val true false))

  Expr
  (evaluate [this] (if val true false))
  (emit [this context objx gen]
    (if val
      (.getStatic gen boolean-object-type "TRUE" boolean-object-type)
      (.getStatic gen boolean-object-type "FALSE" boolean-object-type))
    (pop-if-statement))

  (has-java-class? [this] true)
  (get-java-class [this] Boolean))

(def true-expr (->BooleanExpr true))
(def false-expr (->BooleanExpr false))

(defrecord StringExpr [str]
  LiteralExpr
  (value [this] str)

  Expr
  (evaluate [this] str)
  (emit [this context objx gen]
    (pop-if-statement))
  (has-java-class? [this] true)
  (get-java-class [this] String))

(defn new-string-expr [s] (->StringExpr s))

(defrecord MonitorEnterExpr [target]
  Expr
  (has-java-class? [this] false)
  (get-java-class [this] (throw (IllegalArgumentException. "Has no Java class")))
  (evaluate [this] (throw (UnsupportedOperationException. "Can't eval monitor-enter")))
  (emit [this context objx gen]
    (emit target :expression objx gen)
    (.monitorEnter gen)
    (emit nil-expr context objx gen)))

(defn parse-monitor-enter-expr [context form]
  (->MonitorEnterExpr (analyze :expression (second form))))

(defrecord MonitorExitExpr [target]
  Expr
  (has-java-class? [this] false)
  (get-java-class [this] (throw (IllegalArgumentException. "Has no Java class")))
  (evaluate [this] (throw (UnsupportedOperationException. "Can't eval monitor-exit")))
  (emit [this context objx gen]
    (emit target :expression objx gen)
    (.monitorExit gen)
    (emit nil-expr context objx gen)))

(defn parse-monitor-exit-expr [context form]
  (->MonitorExitExpr (analyze :expression (second form))))

(defrecord CatchClause [^Class c, lb, handler, label, end-label])
(defn new-catch-clause
  ([c lb handler label end-label]
     (map->CatchClause {:c c :lb lb :handler handler
                        :label label :end-label end-label}))
  ([c lb handler]
     (new-catch-clause c lb handler nil nil)))

(defrecord TryExpr [try-expr finally-expr catch-exprs ret-local finally-local]
  Expr
  (has-java-class? [this] (has-java-class? try-expr))
  (get-java-class [this] (get-java-class try-expr))
  (evaluate [this] (throw (UnsupportedOperationException. "Can't eval try")))
  (emit [this context objx gen]
    (let [start-try (.newLabel gen)
          end-try (.newLabel gen)
          end (.newLabel gen)
          ret (.newLabel gen)
          finally-label (.newLabel gen)
          catch-exprs (doall (map #(assoc :label (.newLabel gen)
                                          :end-label (.newLabel gen))
                                  catch-exprs))]
      (.mark gen start-try)
      (emit try-expr context objx gen)
      (when-not (= :statement context)
        (.visitVarInsn gen (.getOpcode object-type Opcodes/ISTORE) ret-local))
      (.mark gen end-try)
      (when finally-expr
        (emit finally-expr :statement objx gen))
      (.goTo gen ret)
      (doseq [clause catch-exprs]
        (doto gen
          (.mark (:label clause))
          (.visitVarInsn (.getOpcode object-type Opcodes/ISTORE) (:idx (:lb clause))))
        (emit (:handler clause) context objx gen)
        (when-not (= :statement context)
          (.visitVarInsn gen (.getOpcode object-type Opcodes/ISTORE) ret-local))
        (.mark gen (:end-label clause))
        (when finally-expr
          (emit finally-expr :statement objx gen))
        (.goTo gen ret))
      (when finally-expr
        (.mark gen finally-label)
        (.visitVarInsn gen (.getOpcode object-type Opcodes/ISTORE) finally-local)
        (emit finally-expr :statement objx gen)
        (.visitVarInsn gen (.getOpcode object-type Opcodes/ILOAD) finally-local)
        (.throwException gen))
      (.mark gen ret)
      (when-not (= :statement context)
        (.visitVarInsn gen (.getOpcode object-type Opcodes/ILOAD) ret-local))
      (.mark gen end)
      (doseq [clause catch-exprs]
        (.visitTryCatchBlock gen start-try end-try (:label clause)
                             (.replace (.getName (:c clause)) "." "/")))
      (when finally-expr
        (.visitTryCatchBlock gen start-try end-try finally-label nil)
        (doseq [clause catch-exprs]
          (doto gen
            (.visitTryCatchBlock (:label clause)
                                 (:end-label clause)
                                 finally-label
                                 nil))))
      (doseq [clause catch-exprs]
        (.visitLocalVariable gen (:name (:lb clause)) "Ljava/lang/Object;" nil
                             (:label clause)
                             (:end-label clause)
                             (:idx (:lb clause)))))))

(defn new-try-expr [try-expr catch-exprs finally-expr ret-local finally-local]
  (map->TryExpr {:try-expr try-expr
                 :catch-exprs catch-exprs
                 :finally-expr finally-expr
                 :ret-local ret-local
                 :finally-local finally-local}))


(defn- op-is-catch-p [f] (and (seq? f) (= 'catch (first f))))
(defn- op-is-finally-p [f] (and (seq? f) (= 'catch (first f))))

(defn- not-catch-or-finally-p [f]
  (not (and (seq? f) (contains? #{'catch 'finally} (first f)))))

(defn- validate-catch-form [f]
  (let [c (maybe-class (second f) false)]
    (if-not c
      (throw (IllegalArgumentException. "Unable to resolve classname: " (second f)))
      (if-not (symbol? (third f))
        (throw (IllegalArgumentException. "Bad binding form, expected symbol, got: "
                                          (third f)))
        (let [sym (third f)]
          (if (namespace sym)
            (throw (RuntimeException. "Can't bind qualified name:" sym))
            f))))))

(defn- parse-catch-clause [context f]
  (validate-catch-form f)
  (let [c (maybe-class (second f))
        sym (third f)]
    (binding [*local-env* *local-env*
              *next-local-num* *next-local-num*
              *in-catch-finally* true]
      (let [lb (register-local sym (when (symbol? (second f)) (second f)) nil false )
            handler (parse-body-expr context (next (next (next f))))]
        (new-catch-clause c lb handler)))))

(defn- parse-finally-clause [f]
  (binding [*in-catch-finally* true]
    (parse-body-expr :statement (next f))))

(defn get-and-inc-local-num []
  (let [num (.intValue *next-local-num*)]
    (if (> num (:max-local *method*))
      (var-set #'*next-local-num* (inc num)))
    num))

(defn parse-try-expr [context form]
  (if-not (= :return context)
    (analyze context (list (list 'fn* [] form)))
    (let [ret-local (get-and-inc-local-num)
          finally-local (get-and-inc-local-num)
          body (doall (take-while not-catch-or-finally-p (next form)))
          body-expr (binding [*no-recur* true] (parse-body-expr context (seq body)))
          remaining (drop-while not-catch-or-finally-p (next form))]
      (when-not (empty? (filter not-catch-or-finally-p remaining))
        (throw (RuntimeException. "Only catch or finally clause can follow catch in try expression")))
      (let [catches (map (partial parse-catch-clause context)
                         (take-while op-is-catch-p remaining))
            remaining (drop-while op-is-catch-p remaining)
            finally-expr (parse-finally-clause (first remaining))]
        (when (next remaining)
          (throw (RuntimeException. "finally clause must be last in try expression")))
        (new-try-expr body-expr catches finally-expr ret-local finally-local)))))

(defrecord EmptyExpr [coll]
  Expr
  (evaluate [this] coll)
  (emit [this context objx gen]
    (let [hashmap-type (Type/getType PersistentArrayMap)
          hashset-type (Type/getType PersistentHashSet)
          vector-type (Type/getType PersistentVector)
          list-type (Type/getType PersistentList)
          empty-list-type (Type/getType PersistentList$EmptyList)]
      (cond
       (list? coll) (.getStatic gen list-type "EMPTY" empty-list-type)
       (vector? coll) (.getStatic gen vector-type "EMPTY" vector-type)
       (map? coll) (.getStatic gen hashmap-type "EMPTY" hashmap-type)
       (set? coll) (.getStatic gen hashset-type "EMPTY" hashset-type)
       :else (throw (UnsupportedOperationException. "Unknown Collection type")))
      (pop-if-statement)))
  (has-java-class? [this] true)
  (get-java-class [this]
    (cond
     (list? coll) IPersistentList
     (vector? coll) IPersistentVector
     (map? coll) IPersistentMap
     (set? coll) IPersistentSet
     :else (throw (UnsupportedOperationException. "Unknown Collection type")))))
(defn new-empty-expr [coll] (->EmptyExpr coll))

(defrecord ConstantExpr [v id]
  Expr
  (evaluate [this] v)
  (emit [this context objx gen]
    (emit-constant objx gen id)
    (pop-if-statement))
  (has-java-class? [this] (Modifier/isPublic (.getModifiers (class v))))
  (get-java-class [this] (class v))

  LiteralExpr
  (value [this] v))

(defn new-constant-expr [v]
  (let [id (register-constant v)]
    (map->ConstantExpr {:v v :id id})))

(defn parse-constant-expr [context form]
  (let [v (second form)]
    (cond
     (nil? v) nil-expr
     (= true v) true-expr
     (= false v) false-expr
     (number? v) (parse-number-expr v)
     (string? v) (new-string-expr v)
     (and (coll? v) (= 0 (count v))) (new-empty-expr)
     :else (new-constant-expr v))))

(defrecord ListExpr [args]
  Expr
  (evaluate [this]
    (seq (into [] (map evaluate args))))
  (emit [this context objx gen]
    (emit-args-as-array args objx gen)
    (.invokeStatic gen rt-type array-to-list-method)
    (pop-if-statement))
  (has-java-class? [this] true)
  (get-java-class [this] IPersistentList))

(defn new-list-expr [args]
  (->ListExpr args))

(defrecord MapExpr [keyvals]
  Expr
  (evaluate [this]
    (let [ret (make-array Object (count keyvals))]
      (doseq [i (range (count keyvals))]
        (aset ret (evaluate (nth keyvals i))))
      (RT/map ret)))
  (emit [this context objx gen]
    (emit-args-as-array keyvals objx gen)
    (.invokeStatic gen rt-type map-method)
    (pop-if-statement))
  (has-java-class? [this] true)
  (get-java-class [this] IPersistentMap))

(defn new-map-expr [keyvals]
  (->MapExpr keyvals))

(defn parse-map-expr [context form]
  (let [mapseq (mapcat (fn [[k v]] [k v]) (seq form))
        keyvals (into [] (map #(analyze (eval-or-expression context) %1) mapseq))
        constant (every? #(satisfies? LiteralExpr %1) keyvals)
        ret (new-map-expr keyvals)]
    (cond
     (and (instance? IObj form) (meta form))
     (new-meta-expr ret (parse-map-expr (eval-or-expression context) (meta form)))

     constant
     (new-constant-expr (let [m (transient {})]
                          (doseq [i (range 0 (count keyvals) 2)]
                            (assoc! m
                                    (value (nth keyvals i))
                                    (value (nth keyvals (inc i)))))
                          (persistent! m)))

     :else ret)))

(defrecord SetExpr [keys]
  Expr
  (evaluate [this]
    (let [ret (make-array Object (count keys))]
      (doseq [i (count keys)]
        (aset ret i (evaluate (nth keys i))))
      (RT/set ret)))
  (emit [this context objx gen]
    (emit-args-as-array keys objx gen)
    (.invokeStatic gen rt-type (Method/getMethod "clojure.lang.IPersistentSet set(Object[])"))
    (pop-if-statement))
  (has-java-class? [this] true)
  (get-java-class [this] IPersistentSet))

(defn new-set-expr [keys]
  (->SetExpr keys))

(defn parse-set-expr [context form]
  (let [keys (into [] (map #(analyze (eval-or-expression context) %1) form))
        constant (every? #(satisfies? LiteralExpr %1) keys)
        ret (new-set-expr keys)]
    (cond
     (and (instance? IObj form) (meta form))
     (new-meta-expr ret (parse-map-expr (eval-or-expression context) (meta form)))

     constant
     (new-constant-expr (let [set (transient #{})]
                          (doseq [i (range (count keys))]
                            (conj! set (value (nth keys i))))
                          (persistent! set)))
     :else ret)))

(defrecord VectorExpr [args]
  Expr
  (evaluate [this] (into [] (map evaluate args)))
  (emit [this context objx gen]
    (let [vector-method (Method/getMethod "clojure.lang.IPersistentVector vector(Object[])")]
      (emit-args-as-array args objx gen)
      (.invokeStatic gen rt-type vector-method)
      (pop-if-statement)))
  (has-java-class? [this] true)
  (get-java-class [this] IPersistentVector))

(defn new-vector-expr [args]
  (->VectorExpr args))

(defn parse-vector-expr [context form]
  (let [args (into [] (map #(analyze (eval-or-expression context) %1) form))
        constant (every? #(satisfies? LiteralExpr %1) args)
        ret (new-vector-expr args)]
    (cond
     (and (instance? IObj form) (meta form))
     (new-meta-expr ret (parse-map-expr (eval-or-expression context) (meta form)))

     constant
     (new-constant-expr (let [rv (transient [])]
                          (doseq [i (range (count args))]
                            (conj! rv (value (nth args i))))
                          (persistent! rv)))
     :else ret)))

(defrecord KeywordInvokeExpr [kw tag target line site-index source]
  Expr
  (evaluate [this]
    (try
      (.invoke (:k kw) (evaluate target))
      (catch Throwable e
        (if (instance? clojure.lang.Compiler$CompilerException e)
          (throw e)
          (throw (clojure.lang.Compiler$CompilerException. source line e))))))
  (emit [this context objx gen]
    (let [end-label (.newLabel gen)
          fault-label (.newLabel gen)]
      (visit-line-number)
      (doto gen
        (.getStatic (:objtype objx)
                    (thunk-name-static objx site-index)
                    ilookup-thunk-type)
        (.dup))
      (emit target :expression objx gen)
      (doto gen
        (.invokeInterface ilookup-thunk-type (Method/getMethod "Object get(Object)"))
        (.dupX2)
        (.visitJumpInsn Opcodes/IF_ACMPEQ fault-label)
        (.pop)
        (.goTo end-label)
        (.mark fault-label)
        (.swap)
        (.pop)
        (.dup)
        (.getStatic (:objtype objx) (site-name-static objx site-index) keyword-lookupsite-type)
        (.swap)
        (.invokeInterface ilookup-site-type (Method/getMethod "clojure.lang.ILookupThunk fault(Object)"))
        (.dup)
        (.putStatic (:objtype objx) (thunk-name-static objx site-index), ilookup-thunk-type)
        (.swap)
        (.invokeInterface ilookup-thunk-type, (Method/getMethod "Object get(Object)"))
        (.mark end-label))
      (pop-if-statement)))
  (has-java-class? [this] (not-nil? tag))
  (get-java-class [this] (tag-to-class tag)))

(defn new-keyword-invoke-expr [source line tag kw target]
  (let [site-index (register-keyword-callsite (:k kw))]
    (map->KeywordInvokeExpr {:kw kw
                             :tag tag
                             :target target
                             :line line
                             :site-index site-index
                             :source source})))

(defrecord InstanceOfExpr [expr c]
  Expr
  (evaluate [this] (if (.isInstance c (evaluate expr)) true false))
  (emit [this context objx gen]
    (emit-unboxed this context objx gen)
    (emit-box-return objx gen Boolean/TYPE)
    (pop-if-statement))
  (has-java-class? [this] true)
  (get-java-class [this] Boolean/TYPE)

  MaybePrimitiveExpr
  (can-emit-primitive [this] true)
  (emit-unboxed [this context objx gen]
    (emit expr :expression objx gen)
    (.instanceOf gen (Type/getType c))))

(defn new-instance-of-expr [c expr]
  (map->InstanceOfExpr {:c c :expr expr}))

(defprotocol EmitProtoExpr
  (emit-proto [this context objx gen])
  (emit-args-and-call [this first-arg-to-emit context objx gen]))

(defrecord InvokeExpr [fexpr tag line protocol? direct? site-index on-method
                       ^IPersistentVector args
                       ^String source
                       ^Class protocol-on]
  Expr
  (evaluate [this]
    (try
      (let [fn (evaluate fexpr)
            argvs (map evaluate args)]
        (.applyTo fn (seq argvs)))
      (catch Throwable e
        (if (instance? clojure.lang.Compiler$CompilerException e)
          (throw e)
          (throw (clojure.lang.Compiler$CompilerException. source line e))))))
  (emit [this context objx gen]
    (visit-line-number)
    (if (protocol?)
      (emit-proto this context objx gen)
      (do
        (emit fexpr :expression objx gen)
        (.checkCast gen ifn-type)
        (emit-args-and-call this 0 context objx gen)))
    (pop-if-statement))
  (has-java-class? [this] (not-nil? tag))
  (get-java-class [this] (tag-to-class tag))

  EmitProtoExpr
  (emit-proto [this context objx gen]
    (let [on-label (.newLabel gen)
          call-label (.newLabel gen)
          end-label (.newLabel gen)
          v (:var fexpr)
          e (first args)]
      (emit e :expression objx gen)
      (doto gen
        (.dup)
        (.invokeStatic util-type, (Method/getMethod "Class classOf(Object)"))
        (.loadThis)
        (.getField (:objtype objx) cached-class-name(objx site-index) class-type)
        (.visitJumpInsn Opcodes/IF_ACMPEQ call-label))
      (when protocol-on
        (doto gen
          (.dup)
          (.instanceOf (Type/getType protocol-on))
          (.ifZCmp GeneratorAdapter/NE, on-label)))
      (doto gen
        (.dup)
        (.invokeStatic util-type (Method/getMethod "Class classOf(Object)"))
        (.loadThis)
        (.swap)
        (.putField (:objtype objx) (cached-class-name site-index) class-type)
        (.mark call-label))
      (emit-var objx gen v)
      (doto gen
        (.invokeVirtual var-type (Method/getMethod "Object getRawRoot()"))
        (.swap))
      (emit-args-and-call this 1 context objx gen)
      (doto gen
        (.goTo end-label)
        (.mark on-label))
      (when protocol-on
        (emit-typed-args objx gen
                         (.getParameterTypes on-method)
                         (subvec args 1 (count args)))
        (emit-clear-locals-if-return)
        (let [m (Method. (.getName on-method)
                         (Type/getReturnType on-method)
                         (Type/getArgumentTypes on-method))]
          (.invokeInterface gen (Type/getType protocol-on) m)
          (emit-box-return objx gen (.getReturnType on-method))))
      (.mark gen end-label)))

  (emit-args-and-call [this first-arg-to-emit context objx gen]
    (doseq [i (range first-arg-to-emit (min max-positional-arity (count args)))]
      (emit (nth args i) :expression objx gen))
    (when (> (count args) max-positional-arity)
      (let [rest-args (into [] (drop max-positional-arity args))]
        (emit-args-as-array rest-args objx gen)))
    (emit-clear-locals-if-return)
    (.invokeInterface gen ifn-type (Method. "invoke" object-type (aget arg-types (min (inc max-positional-arity) (count args)))))))

(defn new-invoke-expr [source line tag fexpr args]
  (let [instance-values (transient {})]
    (assoc! instance-values :source source)
    (assoc! instance-values :fexpr fexpr)
    (assoc! instance-values :args args)
    (assoc! instance-values :line line)

    (when (instance? VarExpr fexpr)
      (let [fvar (:var fexpr)
            pvar (get (meta fvar :protocol))]
        (when (and pvar (bound? #'*protocol-callsites*))
          (let [protocol? true
                site-index (register-protocol-callsite (:var fexpr))
                pon (get (var-get pvar) :on)
                protocol-on (maybe-class pon false)]
            (assoc! instance-values :protocol? protocol?)
            (assoc! instance-values :site-index site-index)
            (assoc! instance-values :protocol-on protocol-on)
            (when protocol-on
              (let [mmap (get (var-get pvar) :method-map)
                    mmap-val (get mmap (keyword (.sym pvar)))]
                (when-not mmap-val
                  (throw (IllegalArgumentException.
                          (str "No method of interface: "
                               (.getName protocol-on)
                               " found for function: "
                               (.sym fvar)
                               " of protocol: "
                               (.sym pvar)
                               " (The protocol method may have been defined before and removed.)"))))
                (let [mname (munge (.. mmap-val sym toString))
                      methods (Reflector/getMethods protocol-on
                                                    (dec (count args))
                                                    mname
                                                    false)]
                  (when-not (= 1 (.size methods))
                    (throw (IllegalArgumentException.
                            (str "No single method: "
                                 mname
                                 " of interface: "
                                 (.getName protocol-on)
                                 " found for function: "
                                 (.sym fvar)
                                 " of protocol: "
                                 (.sym pvar)))))
                  (assoc! instance-values :on-method (.get methods 0)))))))))
    (cond tag
          (assoc! instance-values :tag tag)

          (instance? VarExpr fexpr)
          (let [arglists (get (meta (:var fexpr)) :arglists)
                sig-tag (loop [s (next arglists)]
                          (let [sig (first s)
                                rest-offset (.indexOf sig '&)]
                            (if (or (= (count args) (count sig))
                                    (and (> rest-offset -1)
                                         (>= (count args) (rest-offset))))
                              (tag-of sig)
                              (recur (next s)))))
                tag (if-not sig-tag (:tag fexpr) sig-tag)]
            (assoc! instance-values :tag tag))

          :else
          (assoc! instance-values :tag nil))
    (map->InvokeExpr (persistent! instance-values))))

(defn- check-if-instance-of-expr [context form fexpr]
  (when (and (instance? VarExpr fexpr)
             (= (:var fexpr) #'clojure.core/instance?))
      (when (symbol? (second form))
        (let [c (maybe-class (second form) false)]
          (when c
            (new-instance-of-expr c (analyze context (third form))))))))

(defn- check-if-invoke-prim-expr [context form fexpr]
  (when (and (instance? VarExpr fexpr) (not= :eval context))
    (let [v (:var fexpr)
          arglists (get (meta v) :arglists)
          arity (count (next form))]
      (loop [s (next (seq arglists))]
        (let [args (first s)]
          (when (= arity (count args))
            (let [primc (prim-interface args)]
              (when primc
                (analyze context
                         (apply list
                                '.invokePrim
                                (with-meta (first form) {:tag (symbol primc)})
                                (next form)))))))))))

(defn- check-if-keyword-invoke-expr [context form fexpr]
  (when (and (instance? KeywordExpr fexpr)
           (= 2 (count form))
           (bound? #'*keyword-callsites*))
    (let [target (analyze context (second form))]
      (new-keyword-invoke-expr *source* *line* (tag-of form) fexpr target))))

(defn parse-invoke-expr [ocontext form]
  (let [context (eval-or-expression ocontext)
        fexpr (analyze context (first form))]
    (if-let [instance-of-expr (check-if-instance-of-expr context form fexpr)]
      instance-of-expr
      (if-let [invoke-prim (check-if-invoke-prim-expr context form fexpr)]
        invoke-prim
        (if-let [keyword-invoke-expr (check-if-keyword-invoke-expr context form fexpr)]
          keyword-invoke-expr
          (let [args (into [] (map #(analyze context (first %1)) (seq (next form))))]
            (new-invoke-expr *source* *line* (tag-of form) fexpr args)))))))

(deftype PathNode [type parent])
(defn new-path-node [type parent]
  (->PathNode type parent))

(defn clear-path-root []
  *clear-root*)

(defprotocol IfExprImpl
  (emit-if-expr [this context objx gen emit-unboxed?]))

(defrecord IfExpr [test-expr then-expr else-expr line]
  IfExprImpl
  (emit-if-expr [this context objx gen emit-unboxed?]
    (let [null-label (.newLabel gen)
          false-label (.newLabel gen)
          end-label (.newLabel gen)]
      (visit-line-number)
      (try
        (cond
         (and (instance? StaticMethodExpr test-expr)
              (can-emit-intrinsic-predicate test-expr))
         (emit-intrinsic-predicate test-expr :expression objx gen false-label)

         (= Boolean/TYPE (maybe-primitive-type test-expr))
         (.ifZCmp gen (.EQ gen) false-label)

         :else
         (do
           (emit test-expr :expression objx gen)
           (doto gen
             (.dup)
             (.ifNull null-label)
             (.getStatic boolean-object-type "FALSE" boolean-object-type)
             (.visitJumpInsn Opcodes/IF_ACMPEQ false-label))))

        (catch Exception e
          (throw-runtime e)))

      (if emit-unboxed?
        (emit-unboxed then-expr context objx gen)
        (emit then-expr context objx gen))

      (doto gen
        (.goTo end-label)
        (.mark null-label)
        (.pop)
        (.mark false-label))

      (if emit-unboxed?
        (emit-unboxed else-expr context objx gen)
        (emit else-expr context objx gen))
      (.mark gen end-label)))
  
  Expr
  (evaluate [this]
    (let [t (evaluate test-expr)]
      (if t
        (evaluate then-expr)
        (evaluate else-expr))))
  (emit [this context objx gen]
    (emit-if-expr this context objx gen false))
  (has-java-class? [this]
    (or (and (has-java-class? then-expr)
             (has-java-class? else-expr)
             (= (get-java-class then-expr) (get-java-class else-expr)))
        (and (nil? (get-java-class then-expr))
             (not (.isPrimitive (get-java-class else-expr))))
        (and (nil? (get-java-class else-expr))
             (not (.isPrimitive (get-java-class then-expr))))))
  (get-java-class [this]
    (let [then-class (get-java-class then-expr)]
      (if then-class
        then-class
        (get-java-class else-expr))))
    
    
  MaybePrimitiveExpr
  (emit-unboxed [this context objx gen]
    (emit-if-expr this context objx gen true))
  (can-emit-primitive [this]
    (try
      (and (satisfies? MaybePrimitiveExpr then-expr)
           (satisfies? MaybePrimitiveExpr else-expr)
           (= (get-java-class then-expr) (get-java-class else-expr))
           (can-emit-primitive then-expr)
           (can-emit-primitive else-expr))
      (catch Exception e
        false))))

(defn new-if-expr [line test-expr then-expr else-expr]
  (map->IfExpr {:line line
                :test-expr test-expr
                :then-expr then-expr
                :else-expr else-expr}))

(defn parse-if-expr [context form]
  (cond
   (> (count form) 4) (throw (RuntimeException. "Too many arguments to if"))
   (< (count form) 3) (throw (RuntimeException. "Too few arguments to if"))
   :else
   (let [branch (new-path-node :branch *clear-path*)
         test-expr (analyze (eval-or-expression context) (second form))
         then-expr (binding [*clear-path* (new-path-node :path branch)]
                     (analyze context (third form)))
         else-expr (binding [*clear-path* (new-path-node :path branch)]
                     (analyze context (fourth form)))]
     (new-if-expr *line* test-expr then-expr else-expr))))

(defprotocol CaseExprImpl
  (is-shift-masked? [this])
  (emit-case-expr [this context objx ^GeneratorAdapter gen emit-unboxed?])
  (emit-expr-for-ints [this objx ^GeneratorAdapter gen expr-type default-label])
  (emit-then-for-ints [this objx ^GeneratorAdapter gen
                       expr-type test then default-label emit-unboxed?])
  (emit-expr-for-hashes [this objx ^GeneratorAdapter gen])
  (emit-then-for-hashes [this objx ^GeneratorAdapter gen
                         test then default-label emit-unboxed?])
  (emit-shift-mask [this ^GeneratorAdapter gen])
  (emit-expr [this objx ^GeneratorAdapter gen expr emit-unboxed?]))


(defrecord CaseExpr [expr shift mask low high default-expr
                     ^SortedMap tests ^HashMap thens ^Set skip-check
                     switch-type test-type return-type line]
  Expr
  (has-java-class? [this] (not-nil? return-type))
  (get-java-class [this] return-type)
  (evaluate [this] (throw (UnsupportedOperationException. "Can't eval case")))
  (emit [this context objx gen] (emit-case-expr this context objx gen false))

  MaybePrimitiveExpr
  (can-emit-primitive [this] (primitive? return-type))
  (emit-unboxed [this context objx gen] (emit-case-expr this context objx gen true))

  CaseExprImpl
  (emit-case-expr [this context objx gen emit-unboxed?]
    (let [default-label (.newLabel gen)
          end-label (.newLabel gen)]
      (let [labels (TreeMap.)]
        (doseq [i (.keySet tests)]
          (.put labels i (.newLabel gen)))
        (visit-line-number)
        (let [prim-expr-class (maybe-primitive-type expr)
              prim-expr-type (if prim-expr-class (Type/getType prim-expr-class))]
          (if (= :int test-type)
            (emit-expr-for-ints this objx gen prim-expr-type default-label)
            (emit-expr-for-hashes this objx gen))
          (if (= :sparse switch-type)
            (let [la (make-array Label (.size labels))
                  la (.. labels values (toArray la))
                  ints (Numbers/int-array (.keySet tests))]
              (.visitLookupSwitchInsn gen default-label ints la))
            (let [la (make-array Label (inc (- high low)))]
              (doseq [i (range low (inc high))]
                (aset la (- i low) (if (.containsKey labels i)
                                     (.get labels i)
                                     default-label)))
              (.visitTableSwitchInsn gen low high default-label la)))
          (doseq [i (.keySet labels)]
            (.mark gen (.get labels i))
            (cond (= :int test-type)
                  (emit-then-for-ints this objx gen
                                      prim-expr-type
                                      (.get tests i)
                                      (.get thens i)
                                      default-label
                                      emit-unboxed?)

                  (contains? skip-check i)
                  (emit-expr this objx gen (.get thens i) emit-unboxed?)

                  :else
                  (emit-then-for-hashes this objx gen
                                        (.get tests i)
                                        (.get thens i)
                                        default-label
                                        emit-unboxed?)))
          (.mark gen default-label)
          (emit-expr this objx gen default-expr emit-unboxed?)
          (.mark gen end-label)
          (pop-if-statement)))))
  
  (is-shift-masked? [this] (not= 0 mask))
  (emit-shift-mask [this gen]
    (if (is-shift-masked? this)
      (doto gen
        (.push shift)
        (.visitInsn Opcodes/ISHR)
        (.push mask)
        (.visitInsn Opcodes/IAND))))
  
  (emit-expr-for-ints [this objx gen expr-type default-label]
    (cond (nil? expr-type)
          (do
            (when clojure.core/*warn-on-reflection*
              (print-to-error-writer "Performance warning, %s:%d - case has int tests, but tested expression is not primitive.\n" *source-path* line))
            (emit expr :expression objx gen)
            (doto gen
              (.instanceOf number-type)
              (.ifZCmp GeneratorAdapter/EQ default-label))
            (emit expr :expression objx gen)
            (doto gen
              (.checkCast number-type)
              (.invokeVirtual number-type int-value-method number-type))
            (emit-shift-mask this gen))

          (or (= Type/LONG_TYPE  expr-type)
              (= Type/INT_TYPE   expr-type)
              (= Type/SHORT_TYPE expr-type)
              (= Type/BYTE_TYPE  expr-type))
          (do
            (emit-unboxed expr :expression objx gen)
            (.cast gen expr-type Type/INT_TYPE)
            (emit-shift-mask this gen))

          :else
          (.goTo gen default-label)))
  
  (emit-then-for-ints [this objx gen expr-type test then default-label emit-unboxed?]
    (cond
     (nil? expr-type)
     (do
       (emit expr :expression objx gen)
       (emit test :expression objx gen)
       (.invokeStatic gen util-type equiv-method)
       (.ifZCmp gen GeneratorAdapter/EQ default-label)
       (emit-expr this objx gen then emit-unboxed?))

     (= Type/LONG_TYPE expr-type)
     (do
       (emit-unboxed test :expression objx gen)
       (emit-unboxed expr :expression objx gen)
       (.ifCmp gen Type/LONG_TYPE GeneratorAdapter/NE default-label)
       (emit-expr this objx gen then emit-unboxed))

     (or (= Type/INT_TYPE expr-type)
         (= Type/SHORT_TYPE expr-type)
         (= Type/BYTE_TYPE expr-type))
     (do
       (when (is-shift-masked? this)
         (emit-unboxed test :expression objx gen)
         (emit-unboxed expr-type :expression objx gen)
         (.cast gen expr-type Type/LONG_TYPE)
         (.ifCmp gen Type/LONG_TYPE GeneratorAdapter/NE default-label))
       (emit-expr this objx gen then emit-unboxed))

     :else
     (.goTo gen default-label)))
  
  (emit-expr-for-hashes [this objx gen]
    (let [hash-method (Method/getMethod "int hash(Object)")]
      (emit expr :expression objx gen)
      (.invokeStatic gen util-type hash-method)
      (emit-shift-mask this gen)))

  (emit-then-for-hashes [this objx gen test then default-label emit-unboxed?]
    (emit expr :expression objx gen)
    (emit test :expression objx gen)
    (if (= :hash-identity test-type)
      (.visitJumpInsn Opcodes/IF_ACMPNE default-label)
      (doto gen
        (.invokeStatic util-type equiv-method)
        (.ifZCmp GeneratorAdapter/EQ default-label)))
    (emit-expr this objx gen then emit-unboxed?))
  
  (emit-expr [this objx gen expr emit-unboxed?]
    (if (and emit-unboxed? (satisfies? MaybePrimitiveExpr expr))
      (emit-unboxed expr :expression objx gen)
      (emit expr :expression objx gen))))

(defn new-case-expr [line expr shift mask low high
                     default-expr tests thens
                     switch-type test-type skip-check]
  (let [instance-values (transient {})]
    (assoc! instance-values :expr expr)
    (assoc! instance-values :shift shift)
    (assoc! instance-values :mask mask)
    (assoc! instance-values :low low)
    (assoc! instance-values :high high)
    (assoc! instance-values :default-expr default-expr)
    (assoc! instance-values :tests tests)
    (assoc! instance-values :thens thens)
    (assoc! instance-values :line line)
    (when (and (not= switch-type :compact)
               (not= switch-type :sparse))
      (throw (IllegalArgumentException. (str "Unexpected switch type: " switch-type))))
    (assoc! instance-values :switch-type switch-type)
    (when (and (not= test-type :int)
               (not= test-type :hash-equiv)
               (not= test-type :hash-identity))
      (throw (IllegalArgumentException. (str "Unexpected test type: " + switch-type))))
    (assoc! instance-values :test-type test-type)
    (assoc! instance-values :skip-check skip-check)
    (assoc! instance-values :return-type (maybe-java-class
                                          (doto (ArrayList. (.values thens))
                                            (.add default-expr))))
    (if (and (> (count skip-check) 0)
             clojure.core/*warn-on-reflection*)
      (print-to-error-writer (str "Performance warning, %s:%d - hash collision "
                                  "of some case test constants; if selected, "
                                  "those entries will be tested sequentially.\n"
                                  *source-path* line)))
    (map->CaseExpr (persistent! instance-values))))

(defn parse-case-expr [context form]
  (if (= :eval context)
    (analyze context (list (list ('fn* [] form))))
    (let [args (into [] (next form))
          expr-form (nth args 0)
          shift (.intValue (nth args 1))
          mask (.intValue (nth args 2))
          default-form (nth args 3)
          case-map (nth args 4)
          switch-type (nth args 5)
          test-type (nth args 6)
          skip-check (if (< (count args) 8) nil (nth args 7))
          keys (keys case-map)
          low (.intValue (first keys))
          high (.intValue (nth keys (dec (count keys))))
          test-expr (assoc (analyze :expression expr-form) :should-clear? false)
          tests (TreeMap.)
          thens (HashMap.)
          branch (new-path-node :branch *clear-path*)]
      (doseq [[k pair] (seq case-map)]
        (let [minhash (.intValue k)
              test-expr (if (= :int test-type)
                          (parse-number-expr (.intValue (first pair)))
                          (new-constant-expr (first pair)))]
          (.put tests minhash test-expr)
          (let [then-expr (binding [*clear-path* (new-path-node :path branch)]
                            (analyze context (second pair)))]
            (.put thens minhash then-expr))))
      (let [default-expr (binding [*clear-path* (new-path-node :path branch)]
                           (analyze context (nth args 3)))
            line (.intValue *line*)]
        (new-case-expr line test-expr shift mask low high
                       default-expr tests thens switch-type test-type skip-check)))))
(defn last* [vec]
  (nth vec (dec (count vec))))

(defrecord BodyExpr [exprs]
  Expr
  (evaluate [this]
    (last (map evaluate exprs)))
  (emit [this context objx gen]
    (doseq [e (butlast exprs)]
      (emit e :statement objx gen))
    (emit (last* exprs) context objx gen))
  (has-java-class? [this] (has-java-class? (last* exprs)))
  (get-java-class [this] (get-java-class (last* exprs)))
  
  MaybePrimitiveExpr
  (can-emit-primitive [this]
    (and (satisfies? MaybePrimitiveExpr (last* exprs))
         (can-emit-primitive (last* exprs))))
  (emit-unboxed [this context objx gen]
    (doseq [e (butlast exprs)]
      (emit e :statement objx gen))
    (emit-unboxed (last* exprs) context objx gen))
  )

(defn new-body-expr [exprs]
  (->BodyExpr exprs))

(defn parse-body-expr [context forms]
  (let [forms  (if (= 'do (first forms)) (next forms) forms)
        exprs (transient [])]
    (loop [forms forms]
      (if-not forms
        (do (when (= 0 (count exprs))
              (conj! exprs nil-expr))
            (new-body-expr (persistent! exprs)))
        (let [acontext (if (and (not= :eval context)
                                (or (= :statement context) (not-nil? (next forms))))
                         :statement
                         context)
              e (analyze acontext (first forms))]
          (conj! exprs e)
          (recur (next forms)))))))

(deftype BindingInit [binding init])
(defn new-binding-init [binding init]
  (->BindingInit binding init))

(defn emit-let-fn-inits [fe gen objx lbset]
  (throw (UnsupportedOperationException. "emit-let-fn-inits not implemented")))

(defrecord LetFnExpr [binding-inits body]
  Expr
  (evaluate [this] (throw (UnsupportedOperationException. "Can't eval letfns")))
  (emit [this context objx gen]
    (doseq [bi binding-inits]
      (.visitInsn gen Opcodes/ACONST_NULL)
      (.visitVarInsn gen (.getOpcode object-type Opcodes/ISTORE) (:idx (:binding bi))))
    (let [lbset (transient #{})]
      (doseq [bi binding-inits]
        (let [fe (:init bi)]
          (.visitVarInsn gen (.getOpcode object-type Opcodes/ISTORE)
                         (:idx (:binding bi)))
          (emit-let-fn-inits fe gen objx (persistent! lbset))))
      (loop [loop-label (.mark gen)]
        (emit body context objx gen)
        (let [end (.mark gen)]
          (doseq [bi binding-inits]
            (let [lname (:name (:binding bi))
                  lname (if (.endsWith lname "__auto__")
                          (str lname (RT/nextID))
                          lname)
                  primc (maybe-primitive-type (:init bi))]
              (if primc
                (.visitLocalVariable gen lname (Type/getDescriptor primc)
                                     nil loop-label end (:idx (:binding bi)))
                (.visitLocalVariable gen lname "Ljava/lang/Object;"
                                     nil loop-label end (:idx (:binding bi))))))))))
  (has-java-class? [this] (has-java-class? body))
  (get-java-class [this] (get-java-class body)))

(defn new-let-fn-expr [binding-inits body]
  (map->LetFnExpr {:binding-inits binding-inits
                   :body body}))

(defn parse-let-fn-expr [context form]
  (when-not (vector? (second form))
    (throw (IllegalArgumentException. "Bad binding form, expected vector")))
  (let [bindings (second form)]
    (when-not (= 0 (mod (count bindings) 2))
      (throw (IllegalArgumentException. "Bad binding form, expected matched symbol expression pairs")))
    (let [body (next (next form))]
      (if (= :eval context)
        (analyze context (list (list 'fn* [] form)))
        (binding [*local-env* *local-env*
                  *next-local-num* *next-local-num*]
          (let [lbs (transient [])]
            (doseq [i (range 0 (count bindings) 2)]
              (let [sym (nth bindings i)]
                (when-not (symbol? sym)
                  (throw (IllegalArgumentException.
                          (str "Bad binding form, expected symbol, got: " sym))))
                (when (namespace sym)
                  (throw (RuntimeException. (str "Can't let qualified name: " sym))))
                (let [lb (register-local sym (tag-of sym) nil false)]
                  (conj! lbs (assoc :can-be-cleared? false)))))
            (let [binding-inits (transient [])]
              (doseq [i (range 0 (count bindings) 2)]
                (let [sym (nth bindings i)
                      init (analyze :expression (nth bindings (inc i)))
                      lb (assoc (nth lbs (/ i 2)) :init init)
                      bi (new-binding-init lb init)]
                  (conj! binding-inits bi)))
              (new-let-fn-expr (persistent! binding-inits)
                               (parse-body-expr context body)))))))))


(def specials
  {'def                      parse-def-expr
   'loop*                    parse-let-expr
   'recur                    parse-recur-expr
   'if                       parse-if-expr
   'case*                    parse-case-expr
   'let*                     parse-let-expr
   'letfn*                   parse-let-fn-expr
   'do                       parse-body-expr
   'fn*                      nil
   'quote                    parse-constant-expr
   'var                      parse-the-var-expr
   'clojure.core/import*      parse-import-expr
   '.                        parse-host-expr
   'set!                     parse-assign-expr
   'deftype*                 parse-new-instance-deftype-expr
   'reify*                   parse-new-instance-reify-expr
   'try                      parse-try-expr
   'throw                    parse-throw-expr
   'monitor-enter            parse-monitor-enter-expr
   'monitor-exit             parse-monitor-exit-expr
   'catch                    nil
   'finally                  nil
   'new                      parse-new-expr
   '&                        nil
   })

(defn special? [sym] (contains? specials sym))

(defn close-over [b method]
  (if (and b method)
    (cond (nil? (get (:locals method) b))
          (do
            (assoc! (:closes (:objx method)) b b)
            (close-over b (:parent method)))

          *in-catch-finally*
          (conj! (:locals-used-in-catch-finally method) (.idx b)))))

(defn reference-local [sym]
  (when (bound? #'*local-env*)
    (let [b (get *local-env* sym)]
      (when b
        (close-over b *method*))
      b)))

(defn is-macro [op]
  (cond (and (symbol? op) (reference-local op))
        nil

        (or (symbol? op) (var? op))
        (let [v (if (var? op)
                  op
                  (lookup-var op false false))]
          (when (and v (.isMacro v))
            (if (and (not= *ns* (.ns v)) (not (.isPublic v)))
              (throw (IllegalStateException. (str "var: " v " is not public")))
              v)))))

(defn is-inline [op arity]
  ; no local inlines for now
  (cond (and (symbol? op) (reference-local op))
        nil
        (or (symbol? op) (var? op))
        (let [v (if (var? op)
                  op
                  (lookup-var op false false))]
          (when (and v (.isMacro v))
            (if (and (not= *ns* (namespace v)) (not (.isPublic v)))
              (throw (IllegalStateException. (str "var: " v " is not public")))
              (let [ret (get (meta v) :inline)]
                (when ret
                  (let [arity-pred (get (meta v) :inline-arities)]
                    (when (or (nil? arity-pred) (arity-pred arity))
                      ret)))))))))

(defn names-static-member [sym]
  (and (namespace sym) (nil? (namespace-for sym))))

(defn preserve-tag [src dst]
  (let [tag (tag-of src)]
    (when (and tag (instance? IObj dst))
      (let [mmeta (meta dst)]
        (with-meta dst (assoc mmeta :tag tag))))))

(declare new-local-binding-expr)

(defn analyze-symbol [sym]
  (let [tag (tag-of sym)]
    (if-not (namespace sym)
      (let [b (reference-local sym)]
        (when b
          (new-local-binding-expr b tag)))
      (when (namespace-for sym)
        (let [ns-sym (symbol (namespace sym))
              c (maybe-class ns-sym false)]
          (when c
            (if (Reflector/getField c (name sym) true)
              (new-static-field-expr *line* c (name sym) tag)
              (throw (RuntimeException. (str "Unable to find static field: "
                                             (name  sym)
                                             " in "c))))))))))

(defn- get-line-number [form]
  (if (and (meta form)
           (contains? (meta form) :line))
    (:line (meta form))
    *line*))

(defn macroexpand-1 [form]
  (if (seq? form)
    (let [op (first form)]
       (if (special? op)
         form
         (let [v (is-macro op)]
           (if v
             (try
               (apply v (cons form (cons *local-env* (next form))))
               (catch ArityException e
                 (throw (ArityException. (- (.actual e) 2) (.name e)))))
             (if (symbol? op)
               (let [sym op
                     sname (name sym)]
                 (cond
                  (= \. (.charAt (name sym) 0))
                  (do
                    (when (< (count form) 2)
                      (throw (IllegalArgumentException. "Malformed member expression, expecting (.member target ...)")))
                    (let [meth (symbol (.substring sname 1))
                          target (second form)
                          target (if (maybe-class target false)
                                   (with-meta (list 'clojure.core/identity target)
                                     {:tag 'Class}))]
                      (preserve-tag form (apply list '. target meth (next (next form))))))


                  (names-static-member sym)
                  (let [target (symbol (namespace sym))
                        c (maybe-class target false)]
                    (when c
                      (let [meth (symbol (name symbol))]
                        (preserve-tag form (apply list '. target meth (next form))))))

                  :else
                  (let [idx (.lastIndexOf sname ".")]
                    (when (= idx (dec (.length sname)))
                      (list* 'new (symbol (.substring sname 0 idx)) (next form))))))
               form)))))
    form))

(defn macroexpand
  "Repeatedly calls macroexpand-1 on form until it no longer
  represents a macro form, then returns it.  Note neither
  macroexpand-1 nor macroexpand expand macros in subforms."
  {:added "1.0"
   :static true}
  [form]
    (let [ex (macroexpand-1 form)]
      (if (identical? ex form)
        form
        (macroexpand ex))))

(defn analyze-seq [context form name]
  (let [line (get-line-number form)]
    (binding [*line* line]
      (let [me (macroexpand-1 form)]
        (if-not (= form me)
          (analyze context me name)
          (let [op (first form)]
            (if-not op
              (throw (IllegalArgumentException. "Can't call nil"))
              (let [inline (is-inline op (count (next form)))]
                (if inline
                  (analyze context (preserve-tag form (inline (next form))))
                  (cond (= op 'fn*) (parse-fn-expr context form name)
                        (get specials op)
                        ((get specials op) context form)
                        :else (parse-invoke-expr context form)))))))))))

(defn register-keyword [keyword]
  (if-not (bound? #'*keywords*)
    (new-keyword-expr keyword)
    (let [id (get *keywords* keyword)]
      (when-not id
        (var-set *keywords* (assoc *keywords* keyword (register-constant keyword))))
      (new-keyword-expr keyword))))

(defn- handle-lazy-seq [potentially-lazy-seq]
  (if (instance? LazySeq potentially-lazy-seq)
    (let [form (seq potentially-lazy-seq)]
      (if-not form () (seq form)))
    potentially-lazy-seq))

(defn analyze
  ([context form] (analyze context form nil))
  ([context form name]
     (let [form (handle-lazy-seq form)]
       (try
         (condp = form
           nil nil-expr
           true true-expr
           false false-expr
           (cond
             (symbol? form) (analyze-symbol form)
             (keyword? form) (register-keyword form)
             (number? form) (parse-number-expr form)
             (string? form) (new-string-expr form)

             (and (coll? form) (= 0 (count form)))
             (let [ret (new-empty-expr form)]
               (if (meta form)
                 (new-meta-expr ret (parse-map-expr (eval-or-expression context)
                                                    (meta form)))
                 ret))
             (seq? form) (analyze-seq context form name)
             (vector? form) (parse-vector-expr context form)
             (record? form) (new-constant-expr form)
             (instance? IType form) (new-constant-expr form)
             (map? form) (parse-map-expr context form)
             (set? form) (parse-set-expr context form)))
         (catch Throwable e
           (throw e)
           (if (instance? clojure.lang.Compiler$CompilerException e)
             (throw e)
             (throw (clojure.lang.Compiler$CompilerException. *source-path* *line* e))))))))

(defn eval [form]
  (binding [*loader* (RT/makeClassLoader)
            *line* (get-line-number form)]
    (try
      (let [form (macroexpand form)]
        (cond
         (and (coll? form) (= (first form) 'do))
         (doseq [s (seq form)]
           (eval s))

         (or (instance? IType form)
             (and (coll? form)
                  (not (and (symbol? (first form))
                            (-> form first name (.startsWith "def"))))))
         (do
           (println "here")
           (let [fexpr (analyze :expression
                                (list 'fn* [] form)
                                (str "eval" (RT/nextID)))]
             (let [fn (evaluate fexpr)]
               (.invoke fn))))

         :else
         (do
           (println form)
           (let [expr (analyze :eval form)]
             (println expr)
             (evaluate expr)))))
      (catch Throwable e
        (throw-runtime e)))))