(ns immucode.core
  (:require [immucode.path :as path]
            [immucode.tree :as tree]
            [immucode.utils :as u :refer [cp]]
            [clojure.string :as str]))

(do :help

    (defn append1 [l x]
      (concat l (list x)))

    (defn path->var-sym [p]
      (symbol (str/join "_" p)))

    (defn var->qualified-symbol [v]
      (let [{:keys [ns name]} (meta v)]
        (symbol (str ns) (str name))))

    (defn env->var-sym [env]
      (path->var-sym (tree/position env)))

    (defn cd [env sym]
      (tree/cd env (path/path sym)))

    (defn bubfind [env x]
      (if (symbol? x)
        (tree/find env (path/path x))))

    (defn env-get [env at]
      (tree/cd (tree/root env) (path/path at)))

    (defn expression-subenvs
      [{:as env :keys [expression branch]}]
      (assert (or expression branch))
      (map (fn [idx] (tree/cd env [idx]))
           (range (if expression
                    (count expression)
                    3))))

    (defn resolve-key [env k]
      (if env
        (or (get env k)
            (if-let [link (:link env)]
              (resolve-key (tree/at env link) k))))))

(defn bind

  ([env expr]

   (cp expr

       symbol? (if-let [found (bubfind env expr)]
                 (if (:local found)
                   (assoc env :local (:local found))
                   (assoc env :link (tree/position found)))
                 (if-let [resolved (resolve expr)]
                   (assoc env :var resolved)
                   (u/throw [:unresolvable expr :in env])))

       seq? (if-let [f (-> (bind env (first expr))
                           (resolve-key :bind))]
              (f env (rest expr))
              (reduce (fn [env [idx subexpr]]
                        (bind env idx subexpr))
                      (assoc env :expression expr)
                      (map-indexed vector expr)))

       (assoc env :value expr)))

  ([env sym expr]
   (let [path (path/path sym)]
     (if (tree/cd env path)
       (u/throw [::bind "already defined path" sym env])
       (tree/upd (tree/ensure-path env path)
                 path
                 #(bind % expr))))))

(defn evaluate

  ([{:as env :keys [expression link var value]}]
   (or value
       (if-let [f (:evaluate env)] (f env))
       (cond
         var (deref var)
         link (evaluate (tree/at env link))
         expression (let [[verb & args]
                          (map evaluate
                               (expression-subenvs env))]
                      (apply verb args)))))

  ([env expr]

   (cp expr

       symbol? (if-let [found (bubfind env expr)]
                 (evaluate found)
                 (if-let [resolved (resolve expr)]
                   (deref resolved)
                   (u/throw [:unresolvable expr :in env])))

       seq? (if-let [f (-> (bind env (first expr))
                           (resolve-key :evaluate))]
              (f env (rest expr))
              (let [[verb & args]
                    (map (partial evaluate env) expr)]
                (apply verb args)))

       expr))

  ([env at expr]
   (evaluate (cd env at) expr)))

(def ENV0

  (-> {}
      ;; lambda
      (tree/put '[fn]
                {:evaluate
                 (fn [env [argv return]]
                   (fn [& xs]
                     (-> (reduce (fn [e [argsym argval]]
                                   (tree/put e [argsym] :value argval))
                                 env (zipmap argv xs))
                         (evaluate return))))

                 :bind
                 (fn [env [argv return]]
                   (let [retsym (gensym "ret_")
                         position (tree/position env)
                         name (last position)
                         return-path (conj position retsym)
                         form (list 'fn argv return)
                         initial
                         (-> (tree/put env [name] {:local name})
                             (assoc :lambda form
                                    :name name
                                    :argv argv
                                    :return return-path))]
                     (-> (reduce (fn [e a]
                                   (tree/put e [a] :local a))
                                 initial
                                 argv)
                         (bind retsym return))))})
      ;; let
      (tree/put '[let]
                {:evaluate
                 (fn [env [bindings return]]
                   (let [env+ (reduce (fn [e [argsym argval]]
                                        (tree/put e [argsym] :value (evaluate e argval)))
                                      env (partition 2 bindings))]
                     (evaluate env+ return)))

                 :bind
                 (fn [env [bindings return]]
                   (bind (reduce (fn [e [sym expr]]
                                   (bind e sym expr))
                                 (assoc env :form (list 'let bindings return))
                                 (partition 2 bindings))
                         return))})

      ;; mac
      (tree/put '[mac]
                {:bind (fn [env [argv return]]
                         (let [expand (evaluate env (list 'fn argv return))]
                           (assoc env
                                  :evaluate
                                  (fn [env args]
                                    (evaluate env (expand env args)))
                                  :bind
                                  (fn [env args]
                                    (bind env (expand env args))))))})

      ;; quote
      (tree/put '[quote]
                {:evaluate (fn [_ [x]] (list 'quote x))
                 :bind (fn [env [x]] (assoc env :value (list 'quote x)))})

      (tree/put '[if]
                {:evaluate (fn [env [test then else]]
                             (if (evaluate env test)
                               (evaluate env then)
                               (evaluate env else)))
                 :bind (fn [env [test then else]]
                         (-> (assoc env :branch (list 'if test then else))
                             (bind [0] test)
                             (bind [1] then)
                             (bind [2] else)))})))

(def DEFAULT_COMPILER_OPTS
  {:global-bind-return (fn [bindings return] `(do ~(map (fn [sym val] (list 'def sym val)) bindings) ~return))
   :local-bind-return (fn [bindings return] `(let ~(vec (mapcat identity bindings)) ~return))
   :lambda-compiler (fn [name argv return] `(fn ~@(if (symbol? name) [name]) ~argv ~return))
   :branch-compiler (fn [test then else] (list 'if test then else))
   :application-compiler (fn [& xs] (list* xs))
   :external-symbol-compiler var->qualified-symbol
   :binding-symbol-compiler path->var-sym})

(defn deps
  [{:as env :keys [link expression lambda branch]}]
  (cond
    link (append1 (deps (tree/at env link)) link)
    lambda (remove (partial path/parent-of (tree/position env))
                   (deps (tree/at env (:return env))))
    (or expression branch)
    (reduce
     (fn [ds subenv]
       (let [ds+ (deps subenv)]
         (concat ds+ (remove (set ds+) ds))))
     () (expression-subenvs env))))

(defn build
  [env
   {:as options
    :keys [global-bind-return local-bind-return
           external-symbol-compiler binding-symbol-compiler
           application-compiler lambda-compiler branch-compiler
           captures]}]
  (let [deps (deps env)
        deps (if captures (remove (set captures) deps) deps)]
    (letfn [(build1 [{:as env
                      :keys [local var value link lambda branch expression]}]
              (cond
                local local
                value value
                var (external-symbol-compiler var)
                link (binding-symbol-compiler link)
                expression (apply application-compiler (map build1 (expression-subenvs env)))
                branch (apply branch-compiler (map build1 (expression-subenvs env)))
                lambda (lambda-compiler (:name env)
                                        (:argv env)
                                        (build (tree/at env (:return env))
                                               (assoc options
                                                      :captures deps
                                                      :binding-symbol-compiler
                                                      (fn [p] (binding-symbol-compiler (or (path/remove-prefix p (:return env)) p))))))))]
      (let [bindings
            (map (juxt binding-symbol-compiler (comp build1 (partial tree/at env)))
                 deps)]
        (if (tree/root? env)
          (global-bind-return bindings (build1 env))
          (local-bind-return bindings (build1 env)))))))

(defmacro progn [& xs]
  (let [[head return] (if (odd? (count xs)) [(butlast xs) (last xs)] [xs nil])
        return-binding (if return [(gensym "ret_") return])
        base-bindings (vec (partition 2 head))
        bindings (if return (conj base-bindings return-binding) base-bindings)
        return-sym (first (last bindings))]
    (build (cd (reduce (fn [e [b v]]
                         (bind e b v))
                       ENV0
                       bindings)
               return-sym)
           DEFAULT_COMPILER_OPTS)))

(do :tries

    (do :evaluate
        E1
        (cd E1 '[z 1])
        (evaluate E1 'x)
        (evaluate E1 'x-link)
        (evaluate E1 'z)
        (evaluate E1 'ret)
        ((evaluate ENV0 '(fn [a] a))
         1)
        (evaluate ENV0
                  '((mac [_ args] (list (second args) (first args) (nth args 2)))
                    1 + 2)))

    (do :bind

        (-> ENV0
            (bind 'ret '(let [a 1 b 2] (+ a b)))
            (cd 'ret))

        (-> ENV0
            (bind 'f '(fn [x] (let [a 1 b 2] (+ x a b))))
            (bind 'ret '(f 1))
            (cd 'ret))

        (def E1
          (-> ENV0
              (bind 'x 1)
              (bind 'x-link 'x)
              (bind 'y 2)
              (bind 'a 34)
              (bind 'z '(+ x y))
              (bind 'ret '(+ z z))
              (bind 'fun '(fn [a b c] (+ a b c z)))
              (bind 'ret2 '(fun x ret a)))))

    (do :build
        (build (cd E1 'ret)
               DEFAULT_COMPILER_OPTS)

        (eval (build (cd E1 'ret2)
                     DEFAULT_COMPILER_OPTS))

        (-> ENV0
            (bind 'y 23)
            (bind 'f '(fn [x] (let [a 1 b 2] (+ y x a b))))
            (bind 'ret '(f 1))
            (cd 'ret)
            (build DEFAULT_COMPILER_OPTS)))

    (do :progn

        :simple

        (progn x 1 y 2 (+ x y))

        (progn x 1
               f (fn [a b] (let [y 4] (+ x y a b)))
               (f 4 5))

        :lambda

        (progn ((fn [a b] (+ a b)) 1 2))

        :nested-bindings

        (progn x 1
               y (let [z 3] (+ x z))
               (+ y.z x y))

        :mac

        (progn infix (mac [_ args] (list (second args) (first args) (nth args 2)))
               (infix 1 + 2))

        (progn ((mac [_ args] (list (second args) (first args) (nth args 2)))
                1 + 2))

        (bind ENV0 'infix '(mac [_ args] (list (second args) (first args) (nth args 2))))

        :quote

        (progn 'io)

        :if

        (progn (if true :ok :ko))
        (progn (if (= 1 ((fn [a] a) 2))
                 (let [x 1 y 2] (+ x y))
                 'ko))

        :recursion

        (bind ENV0 'f '(fn [x] (if (pos? x) (f (dec x)) :done)))
        (progn f (fn [x] (if (pos? x) (f (dec x)) :done))
               (f 10))

        ()
        ))
