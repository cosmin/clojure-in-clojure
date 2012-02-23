(ns clojure-compiler.core
  (:refer-clojure :exclude [*source-path* *compile-path* *compile-files*])
  (:import [clojure.lang IFn AFunction IPersistentMap IObj])
  (:import [clojure.lang Keyword Var Symbol Namespace])
  (:import [clojure.lang RT Numbers  Util Reflector])
  (:import [clojure.asm Type])
  (:import [clojure.asm.commons GeneratorAdapter Method])
  (:import [java.lang.reflect Constructor Modifier])
  (:import [java.util.regex Pattern]))

(defn third [coll]
  (first (next (next coll))))

(defn fourth [coll]
  (first (next (next (next coll)))))

(defn- lookup-var* [sym intern-new?]
  (cond (not (nil? (namespace sym)))
        (let [ns (namespace-for sym)]
          (if (nil? ns)
            nil
            (let [name (symbol (name nil sym))]
              (if (and intern-new? (= ns *ns*))
                (.intern *ns* name)
                (.findInternedVar ns name)))))
        TODO
        
        )
  )

(defn lookup-var
  ([sym intern-new?] (lookup-var sym intern-new? true))
  ([sym intern-new? register-macro?]
     (let [lookup-var* (fn [])])
     ))


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

(defprotocol Expr
  (evaluate [this])
  (emit [this context objx ^GeneratorAdapter gen])
  (^boolean has-java-class? [this])
  (^Class get-java-class [this]))

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

(defn- lookup-var-in-current-ns [sym]
  (let [v (lookup-var sym true)]
    (if (nil? v)
      (throw (RuntimeException. "Can't refer to qualified var that doesn't exist"))
      (if (not (= (namespace v) *ns*))
        (if (nil? (namespace sym))
          (.intern *ns* sym)
          (throw (RuntimeException. "Can't create defs outside of current ns")))))))

(defn- meta-add-source-line-doc [mm docstring]
  (let [source-path (if (nil? *source-path*) "NO_SOURCE_FILE" *source-path*)
        mm (assoc mm :line *line* :file source-path)]
    (if (not (nil? docstring))
      (assoc mm :doc docstring)
      mm)))

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
      
      (not (instance? Symbol (second form)))
      (throw (RuntimeException. "First argument to def must be a Symbol")))
     (let [sym (second form)
           v (lookup-var-in-current-ns sym)
           mm (meta sym)
           dynamic? (:dynamic mm)]
       (if (dynamic?)
         (.setDynamic v)
         (if (and (.startsWith (name sym) "*")
                  (.endsWith (name sym) "*")
                  (> 1 (.length (name sym))))
           (.. RT
               errPrintWriter
               (format
                (str "Warning: %1$s not declared dynamic "
                     "and thus is not dynamically rebindable, "
                     "but its name suggests otherwise. "
                     "Please either indicate ^:dynamic %1$s "
                     "or change the name. (%2$s:%3$d)\n")
                sym *source-path*, *line*)))
         (if (:arglists mm)
           (let [vm (meta v)]
             (.setMeta v (assoc vm :arglists (second (:arglists mm))))))
         (let [mm (meta-add-source-line-doc mm docstring)
               mcontext (if (= ::eval context) context ::expression)
               meta (if (= 0 (count mm)) nil (analyze mcontext mm))]
           (new DefExpr {:source *source*
                         :line *line*
                         :var v
                         :init (analyze mcontext (third form))
                         :meta meta
                         :init-provided? (= 3 (count form))
                         :dynamic? dynamic?}))))))