(ns clojure.compiler
  (:refer-clojure :exclude [*source-path* *compile-path* *compile-files* munge])
  (:use clojure.utilities)
  (:use [clojure.runtime :only (namespace-for lookup-var print-to-error-writer)])
  (:use [clojure.compiler.helpers :only (lookup-var-in-current-ns)])
  (:use [clojure.compiler.primitives])
  (:import [clojure.lang IFn AFunction IPersistentMap IObj])
  (:import [clojure.lang Keyword Var Symbol Namespace])
  (:import [clojure.lang RT Numbers  Util Reflector])
  (:import [clojure.asm Type])
  (:import [clojure.asm.commons GeneratorAdapter Method])
  (:import [java.lang.reflect Constructor Modifier])
  (:import [java.util.regex Pattern]))

(def TODO nil)

(declare analyze)
(declare emit-var)
(declare emit-var-value)
(declare emit-keyword)
(declare emit-nil-expr)
(declare host-expr-tag->class)

(declare def-expr-parser)
(declare let-expr-parser)
(declare recur-expr-parser)
(declare if-expr-parser)
(declare case-expr-parser)
(declare let-expr-parser)
(declare let-fn-expr-parser)
(declare body-expr-parser)
(declare constant-expr-parser)
(declare the-var-expr-parser)
(declare import-expr-parser)
(declare host-expr-parser)
(declare assign-expr-parser)
(declare new-instance-deftype-expr-parser)
(declare new-instance-reify-expr-parser)
(declare try-expr-parser)
(declare throw-expr-parser)
(declare monitor-enter-expr-parser)
(declare monitor-exit-expr-parser)
(declare new-expr-parser)

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

(def specials
  {'def                      def-expr-parser
   'loop*                    let-expr-parser
   'recur                    recur-expr-parser
   'if                       if-expr-parser
   'case*                    case-expr-parser
   'let*                     let-expr-parser
   'letfn*                   let-fn-expr-parser
   'do                       body-expr-parser
   'fn                       nil
   'quote                    constant-expr-parser
   'var                      the-var-expr-parser
   'clojure.core/import*      import-expr-parser
   '.                        host-expr-parser
   'set!                     assign-expr-parser
   'deftype*                 new-instance-deftype-expr-parser
   'reify*                   new-instance-reify-expr-parser
   'try                      try-expr-parser
   'throw                    throw-expr-parser
   'monitor-enter            monitor-enter-expr-parser
   'monitor-exit             monitor-exit-expr-parser
   'catch                    nil
   'finally                  nil
   'new                      new-expr-parser
   '&                        nil
   })

(defn special? [sym] (contains? specials sym))

(def max-positional-arity 20)

(defmacro defasmtype [name klass]
  `(def ~name (Type/getType ~klass)))

(defasmtype object-type Object)
(defasmtype keyword-type Keyword)
(defasmtype var-type Var)
(defasmtype symbol-type Symbol)
(defasmtype ifn_type IFn)
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
  (let [source-path (if (nil? *source-path*) "NO_SOURCE_FILE" *source-path*)
        mm (assoc mm :line *line* :file source-path)]
    (if (not (nil? docstring))
      (assoc mm :doc docstring)
      mm)))



(defprotocol Expr
  (evaluate [this])
  (emit [this context objx ^GeneratorAdapter gen])
  (^boolean has-java-class? [this])
  (^Class get-java-class [this]))

(defprotocol AssignableExpr
  (eval-assign [this val])
  (emit-assign [this context objx gen val]))

(defprotocol LiteralExpr
  (value [this]))

(defprotocol MaybePrimitiveExpr
  (^boolean can-emit-primitive [this])
  (emit-unboxed [this context, ^clojure.compiler.ObjExpr objx,^GeneratorAdapter gen]))

(defn eval-or-expression [context]
  (if (= ::eval context) context ::expression))

(declare FnExpr)

(defrecord DefExpr [^Var var, init, meta,
                    ^boolean init-provided?, ^boolean dynamic?,
                    ^String source, ^long line]
  Expr
  (evaluate [this]
    (if init-provided?
      (.bindRoot var (evaluate init)))
    (if (not (nil? meta))
      (.setMeta (evaluate meta)))
    (.setDynamic var dynamic?))
  (emit [this context objx gen]
    (let [bind-root-method (Method/getMethod "void bindRoot(Object)")
          set-tag-method  (Method/getMethod "void setTag(clojure.lang.Symbol)")
          set-meta-method  (Method/getMethod "void setMeta(clojure.lang.IPersistentMap)")
          set-dynamic-method  (Method/getMethod "clojure.lang.Var setDynamic(boolean)")
          symintern  (Method/getMethod "clojure.lang.Symbol intern(String, String)")]
      (.emitVar objx gen var)
      (if dynamic?
        (do
          (.push gen dynamic?)
          (.invokeVirtual gen var-type set-dynamic-method)))
      (if (not (nil? meta))
        (do
          (.dup gen)
          (emit meta ::expression objx gen)
          (.checkCast gen ipersistent-map-type)
          (.invokeVirtual gen var-type set-meta-method)))
      (if init-provided?
        (do
          (.dup gen)
          (if (instance? FnExpr init)
            (.emitForDefn init objx gen)
            (emit init ::expression objx gen))
          (.invokeVirtual gen var-type bind-root-method)))
      (if (= ::statement context)
        (.pop gen))))
  (has-java-class? [init] true)
  (get-java-class [init] Var))

(defn def-expr-parser
  ([context form]
     (if (and (= 4 (count form)) (string? (third form)))
       (def-expr-parser
         context
         (list (first form) (second form) (fourth form))
         (third form))
       (def-expr-parser context form nil)))
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
       (if (dynamic?)
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
       (if (:arglists mm)
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

(defn assign-expr-parser [context form]
  (if  (not= 3 (count form))
    (throw (IllegalArgumentException. "Malformed assignment, expecting (set! target val)"))
    (let [target (analyze ::expression (second form))]
      (if (not (instance? AssignableExpr target))
        (throw (IllegalArgumentException. "Invalid assignment target"))
        (map->AssignExpr {:target target
                          :val (analyze ::expression (third form))})))))


(defrecord VarExpr [^Var var, tag]
  Expr
  (evaluate [this] (.deref var))
  (emit [this context objx gen]
    (emit-var-value objx gen var)
    (if (== ::statement context)
      (.pop gen)))
  (has-java-class? [this] (not (nil? tag)))
  (get-java-class [this] (host-expr-tag->class tag))

  AssignableExpr
  (eval-assign [this val] (var-set var (evaluate val)))
  (emit-assign [this context objx gen val]
    (let [set-method (Method/getMethod "Object set(Object)")]
      (emit-var objx var)
      (emit val ::expression objx gen)
      (.invokeVirtual gen var-type set-method)
      (if (= ::statement context)
        (.pop gen)))))

(defrecord TheVarExpr [^Var var]
  Expr
  (evaluate [this] var)
  (emit [this context objx gen]
    (emit-var objx gen var)
    (if (= ::statement context)
      (.pop gen)))
  (has-java-class? [this] true)
  (get-java-class [this] Var))


(defn the-var-expr-parser [context form]
  (let [sym (second form)
        v (lookup-var sym false)]
    (if (not (nil? v))
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
    (if (= ::statement context)
      (.pop gen)))
  (has-java-class? [this] true)
  (get-java-class [this] Keyword))

(defrecord ImportExpr [^String c]
  Expr
  (evaluate [this]
    (do
      (.importClass *ns* (RT/classForName c))
      nil))

  (emit [this context objx gen]
    (let [for-name-method (Method/getMethod "Class forName(String)")
          import-class-method (Method/getMethod "Class importClass(Class)")
          deref-method (Method/getMethod "Object deref()")]
      (doto gen
        (.genStatic rt-type "CURRENT_NS" var-type)
        (.invokeVirtual var-type deref-method)
        (.checkCast ns-type)
        (.push c)
        (.invokeStatic class-type for-name-method)
        (.invokeVirtual ns-type import-class-method))
      (if (= ::statement context)
        (.pop gen))))

  (has-java-class? [this] false)
  (get-java-class [this] (throw (IllegalArgumentException. "ImportExpr has no Java class"))))

(defn import-expr-parser [context form]
  (->ImportExpr (second form)))

(defn emit-box-return [objx, ^GeneratorAdapter gen, ^Class return-type]
  (if (.isPrimitive return-type)
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

      Void/TYPE (emit-nil-expr ::expression objx gen)
      Character/TYPE (.invokeStatic gen char-type char-value-of-method)
      Integer/TYPE (.invokeStatic gen integer-type int-value-of-method)
      Float/TYPE (.invokeStatic gen float-type float-value-of-method)
      Double/TYPE (.invokeStatic gen double-type double-value-method)
      Long/TYPE (.invokeStatic gen number-type (Method/getMethod "Number num(long)"))
      Byte/TYPE (.invokeStatic gen byte-type byte-value-of-method)
      Short/TYPE (.invokeStatic gen short-type short-value-of-method))))


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

(defn maybe-class [form, string-ok?]
  (cond
   (class? form)
   form

   (symbol? form)
   (let [sym form]
     (if (nil? (namespace sym)) ; if ns-qualified can't be classname
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
        array-class (if (symbol? tag)
                      (let [sym tag]
                        ; if ns-qualified can't be classname
                        (if (nil? (namespace sym))
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
    (if (not-nil? array-class)
      array-class
      (if (not-nil? c)
        c
        (throw (IllegalArgumentException.
                (str "Unable to resolve classname: " tag)))))))

(defn- represents-static? [sym]
  (not= \- (.charAt (name sym) 0)))

(defn- is-field? [c instance sym]
  (if (represents-static? sym)
    (if (not-nil? c)
      (= 0 (.size (Reflector/getMethods c 0 (munge (name sym)) true)))
      (if (and (not-nil? instance)
               (.hasJavaClass instance)
               (not-nil? (.getJavaClass instance)))
        (= 0 (.size (Reflector/getMethods (.getjavaclass instance) 0 (munge (name sym)) false)))
        ))))

(defn- tag-of [o]
  (let [tag (:tag (meta o))]
    (cond
     (symbol? tag) tag
     (string? tag) (symbol nil tag)
     :else nil)))

(defn new-static-field-expr [line c field-name tag]
  TODO)

(def invoke-no-arg-instance-member
  (Method/getMethod "Object invokeNoArgInstanceMember(Object,String)"))
(def set-instance-field-method
  (Method/getMethod "Object setInstanceField(Object,String,Object)"))

(defrecord InstanceFieldExpr [target target-class field field-name line tag]
  Expr
  (evaluate [this]
    (Reflector/invokeNoArgInstanceMember (evaluate target) field-name))
  (emit [this context objx gen]
    (.visitLineNumber gen line (.mark gen))
    (if (and (not-nil? target-class) (not-nil? field))
      (do (emit target ::expression objx gen)
          (doto gen
            (.checkCast (Type/getType target-class))
            (.getField (Type/getType target-class)
                       field-name
                       (Type/getType (.getType field))))
          (emit-box-return objx gen (.getType field))
          (if (= ::statement context)
            (.pop gen)))
      (do (emit target ::expression objx gen)
          (doto gen
            (.push field-name)
            (.invokeStatic reflector-type invoke-no-arg-instance-member))
          (if (= ::statement context)
            (.pop gen)))))
  (has-java-class? [this] (or (not-nil? field) (not-nil? tag)))
  (get-java-class [this]
    (if (not-nil? tag)
      (tag-to-class tag)
      (.getType field)))
    
  MaybePrimitiveExpr
  (can-emit-primitive [this]
    (and (not-nil? target-class)
         (not-nil? field)
         (primitive? (.getType field))))
  (emit-unboxed [this context objx gen]
    (.visitLineNumber gen line (.mark gen))
    (if (and (not-nil? target-class) (not-nil? field))
      (do (emit target ::expression objx gen)
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
    (.visitLineNumber gen line (.mark gen))
    (if (and (not-nil? target-class) (not-nil? field))
      (do (emit target ::expression objx gen)
          (.checkCast gen (Type/getType target-class))
          (emit val ::expression objx gen)
          (.dupX1 gen)
          (emit-unbox-arg objx gen (.getType field))
          (.putField gen
                     (Type/getType target-class)
                     field-name
                     (Type/getType (.getType field))))
      (do (emit target ::expression objx gen)
          (.push gen field-name)
          (emit val ::expression objx gen)
          (.invokeStatic gen reflector-type set-instance-field-method)
          )
      )
    )
  
  )

(defn new-instance-field-expr [line target field-name tag]
  (let [target-class (if (has-java-class? target) (get-java-class target))
        field (if (not-nil? target-class) (Reflector/getField target-class field-name false))]
    (if (and (nil? field) clojure.core/*warn-on-reflection*)
      (print-to-error-writer "Reflection warning, %s:%d - reference to field %s can't be resolved.\n" *source-path* line field-name))
    (map->InstanceFieldExpr {:target target
                             :target-class target-class
                             :field field
                             :field-name field-name
                             :line line
                             :tag tag})))

(defn new-static-method-expr [source line tag c method-name tag]
  TODO)

(defn new-instance-method-expr [source line tag target method-name args]
  TODO)



(defn host-expr-parser [context form]
  (if (< (count form) 3)
    (throw (IllegalArgumentException. "malformed member expression, expecting (. target member ...)")))
  (let [c (maybe-class (second form false))
        icontext (eval-or-expression context)
        instance (if (nil? c) (analyze icontext (second form)))
        third-form (third form)
        maybe-field (and (= 3 (count form)) (symbol? third-form))
        field? (if maybe-field (is-field? c instance third-form))]
    (if field?
      (let [sym (if (represents-static? third-form)
                  (symbol (.substring (name third-form) 1))
                  third-form)
            tag (tag-of form)
            field-name (munge (name sym))]
        (if (not-nil? c)
          (new-static-field-expr *line* c field-name tag)
          (new-instance-field-expr *line* instance field-name tag)))
      (let [call (if (seq? third-form) third-form (next (next form)))]
        (if (not (symbol? (first call)))
          (throw (IllegalArgumentException. "Malformed member expression")))
        (let [sym (first call)
              tag (tag-of form)
              args (into [] (map #(analyze (eval-or-expression context) %1)))
              field-name (munge (name sym))]
          (if (not-nil? c)
            (new-static-method-expr *source* *line* tag c field-name args)
            (new-instance-method-expr *source* *line* tag instance field-name args)))))))