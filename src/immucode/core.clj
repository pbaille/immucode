(ns immucode.core
  (:refer-clojure :exclude [compile])
  (:require [immucode.path :as path]
            [immucode.tree :as tree]
            [immucode.utils :as u :refer [cp]]
            [immucode.composite-literals :as composite]
            [immucode.destructure :as destructure]
            [immucode.quote :as quote]
            [clojure.string :as str]
            [immucode.control :as control]))

(do :help

    (defn append1 [l x]
      (concat l (list x)))

    (defn path->binding-symbol [p]
      (symbol (str/join "_" p)))

    (defn var->qualified-symbol [v]
      (let [{:keys [ns name]} (meta v)]
        (symbol (str ns) (str name))))

    (defn env->var-sym [env]
      (path->binding-symbol (tree/position env)))

    (defn cd [env sym]
      (tree/cd env (path/path sym)))

    (defn bubfind [env x]
      (if (and (symbol? x)
               (not (namespace x)))
        (tree/find env (path/path x))))

    (defn env-get [env at]
      (tree/cd (tree/root env) (path/path at)))

    (defn target-node [env]
      (if-let [link (:link env)]
        (target-node (tree/at env link))
        env))

    (defn resolve-key [env k]
      (get (target-node env) k))

    (defn pairs&return [xs]
      (if (odd? (count xs))
        [(partition 2 (butlast xs)) (last xs)]
        [(partition 2 xs) nil]))

    (defn deps-merge [old new]
      (concat new (remove (set new) old)))

    (defn sequential-children
      [env]
      (->> (tree/children env)
           (filter (comp int? ::tree/name))
           (sort-by ::tree/name))))

(defn bind

  "Load some expressions into the given environment"

  ([env expr]

   (if (tree/root? env)

     (u/throw
      [::bind "cannot bind at top level:" expr])

     (cp expr

         symbol? (if-let [found (bubfind env expr)]
                   (let [at (tree/position env)
                         target (update found :referenced-by conj at)]
                     (-> (tree/at target at)
                         (assoc :link (tree/position target))))
                   (bind env (list 'external expr)))

         seq? (if-let [f (-> (bind env (first expr))
                             (resolve-key :bind))]
                (f env (rest expr))
                (bind env (cons 's-expr expr)))

         vector? (bind env (cons 'vector expr))

         map? (bind env (cons 'hash-map expr))

         (bind env (list 'value expr)))))

  ([env sym expr]
   (let [path (path/path sym)]
     (if-let [found (tree/cd env path)]
       (u/throw [::bind "already defined path:"
                 (tree/position found)])
       (tree/upd (tree/ensure-path env path)
                 path #(bind % expr)))))

  ([env sym expr & more]
   (let [[bindings return] (pairs&return (list* sym expr more))
         bound (reduce (fn [env [sym expr]] (bind env sym expr))
                       env bindings)]
     (if return
       (bind bound return)
       bound))))

(defn evaluate
  [env]
  (let [target-node (target-node env)]
    (if (contains? target-node :value)
      (get target-node :value)
      (if-let [evaluate (resolve-key env :evaluate)]
        (evaluate env)
        (u/throw [::evaluate "no :value nor :evaluate at:"
                  (tree/position env)])))))

(defn interpret

  ([env expr]

   (cp expr

       symbol? (if-let [found (bubfind env expr)]
                 (evaluate found)
                 (interpret env (list 'external expr)))

       seq? (if-let [f (-> (bind env (first expr))
                           (resolve-key :interpret))]
              (f env (rest expr))
              (interpret env (cons 's-expr expr)))

       vector? (interpret env (cons 'vector expr))

       map? (interpret env (cons 'hash-map expr))

       expr))

  ([env at expr]
   (if-let [env (cd env at)]
     (interpret env expr)
     (u/throw [::interpret "non existant location:"
               (path/path at) "from:"
               (tree/position env)]))))

(defn outer-links
  "return all links pointing outside the current node"
  [env]
  (if-let [target (:link env)]
    (list target)
    (->> (map outer-links (tree/children env))
         (reduce deps-merge ())
         (remove (partial path/parent-of (tree/position env))))))

(defn transitive-deps
  [env]
  (loop [ret () todo (outer-links env)]
    (if (seq todo)
      (let [next-ret (deps-merge ret todo)]
        (recur next-ret
               (->> todo
                    (map (partial tree/at env))
                    (map outer-links)
                    (reduce deps-merge ())
                    (remove (set next-ret)))))
      ret)))

(defn build
  [env]
  (if (contains? env :value) ; handling falsy values
    (get env :value)
    (if-let [build (:build env)]
      (build env)
      (if-let [target-path (:link env)]
        (let [target (tree/at env target-path)]
          (if (:local target)
            (last target-path)
            (path->binding-symbol target-path)))
        (u/throw [::build "no :build nor :value fields at:"
                  (tree/position env)])))))

(defn compile
  [env]
  (if-let [compile (resolve-key env :compile)]

    (compile env)

    (if-let [bindings
             (some->> (seq (transitive-deps env))
                      (mapcat (fn [p] [(path->binding-symbol p)
                                      (build (tree/at env p))])))]
      (list 'let (vec bindings) (build env))
      (build env))))

(def ENV0

  (-> {}

      ;; base
      (tree/put '[value]
                {:bind
                 (fn [env [v]]
                   (let [type (u/simple-type v)]
                     (assoc env
                            :value v
                            :type type
                            type true)))})

      (tree/put '[external]
                {:interpret
                 (fn [env [sym]]
                   (if-let [resolved (resolve sym)]
                     (deref resolved)
                     (u/throw [:unresolvable sym :in env])))
                 :bind
                 (fn [env [sym]]
                   (if-let [resolved (resolve sym)]
                     (if (= resolved #'clojure.core/unquote)
                       (bind env 'eval)
                       (assoc env
                              :external resolved
                              :build (fn [_] (var->qualified-symbol resolved))))
                     (u/throw [:unresolvable sym :in env])))})

      (tree/put '[s-expr]
                {:interpret
                 (fn s-expr-interpret [env expr]
                   (if (composite/composed? expr)
                     (interpret env (composite/expand-seq expr))
                     (let [[verb & args]
                           (map (partial interpret env) expr)]
                       (apply verb args))))

                 :bind
                 (fn s-expr-bind [env expr]
                   (if (composite/composed? expr)
                     (bind env (composite/expand-seq expr))
                     (-> (reduce (fn [env [idx subexpr]]
                                   (bind env idx subexpr))
                                 (assoc env :s-expr expr)
                                 (map-indexed vector expr))
                         (assoc
                          :build
                          (fn s-expr-instance-build [env]
                            (map build (sequential-children env)))))))})

      ;; let
      (tree/put '[let1]
                {:interpret
                 (fn let1-interpret
                   [env [[pattern expr] return]]
                   (-> (reduce (fn [e [argsym argval]]
                                 (tree/put e [argsym] :value (interpret e argval)))
                               env (partition 2 (destructure/bindings pattern expr {})))
                       (interpret return)))

                 :bind
                 (fn let1-bind
                   [env [[pattern expr] return :as args]]

                   (let [return-symbol '__return__

                         bindings
                         (partition 2 (destructure/bindings pattern expr {}))

                         bound
                         (reduce (fn [e [sym expr]]
                                   (-> (bind e sym expr)
                                       (tree/put [sym] :local true)))
                                 env bindings)]

                     (-> (bind bound
                               return-symbol
                               return)

                         (assoc
                          :let1 (cons 'let1 args)
                          :build
                          (fn let1-instance-build [env]
                            (let [bindings
                                  (map (fn [sym]
                                         [sym (build (cd env sym))])
                                       (map first bindings))]
                              (list 'let
                                    (reduce into [] bindings)
                                    (build (cd env return-symbol)))))))))})

      (tree/put '[let]
                ;; TODO add named let (using lambda)
                {:interpret
                 (fn let-interpret [env [bindings return]]
                   (interpret env
                              (reduce (fn [ret binding] (list 'let1 binding ret))
                                      return (reverse (partition 2 bindings)))))

                 :bind
                 (fn let-bind [env [bindings return]]
                   (bind env
                         (reduce (fn [ret binding] (list 'let1 binding ret))
                                 return (reverse (partition 2 bindings)))))})

      ;; lambda
      (tree/put '[fn]
                {:interpret
                 (fn [env [argv return]]
                   (fn [& xs]
                     ;; TODO add recursion
                     (-> (reduce (fn [e [argsym argval]]
                                   (tree/put e [argsym] :value argval))
                                 env (zipmap argv xs))
                         (interpret return))))

                 :bind
                 (fn [env [argv return]]

                   (let [form (list 'fn argv return)
                         position (tree/position env)
                         fn-name (last position)
                         return-symbol '__return__
                         return-path (conj position return-symbol)

                         arguments
                         (map-indexed (fn [idx p]
                                        (if (symbol? p)
                                          {:symbol p}
                                          {:symbol (gensym (str "arg" idx))
                                           :destructure p}))
                                      argv)

                         argument-symbols
                         (mapv :symbol arguments)

                         with-locals
                         (reduce (fn [e a]
                                   (tree/put e [a] :local a))
                                 (assoc env :lambda form)
                                 (cons fn-name argument-symbols))

                         destructuration-bindings
                         (mapcat (juxt :destructure :symbol)
                                 (filter :destructure arguments))

                         return-expression
                         (if (seq destructuration-bindings)
                           (list 'let destructuration-bindings return)
                           return)]

                     (-> (bind with-locals
                               return-symbol
                               return-expression)

                         (assoc
                          :build
                          (fn lambda-instance-build [env]
                            (let [return (build (tree/at env return-path))]
                              (if (symbol? fn-name)
                                (list 'fn fn-name argument-symbols return)
                                (list 'fn argument-symbols return))))))))})

      ;; module
      (tree/put '[module]
                {:interpret ()
                 :bind (fn [env args]
                         (let [env (assoc env :module true)]
                           (if (vector? (first args))
                             (assoc env
                                    :parametric true
                                    :bind (fn [env2 parameters]
                                            (-> (reduce (fn [e [sym expr]] (bind e sym expr))
                                                        env2 (map vector (first args) parameters))
                                                (bind (cons 'module (next args))))))
                             (apply bind env args))))})

      ;; eval
      (tree/put '[eval]
                {:interpret
                 (fn [env [expr]]
                   (interpret env expr))
                 :bind
                 (fn [env [expr]]
                   (bind env (interpret env expr)))})

      ;; mac
      (tree/put '[mac]
                {:bind
                 (fn [env [argv return]]
                   (let [expand (interpret env (list 'fn argv return))]
                     (assoc env
                            :interpret
                            (fn [env args]
                              (interpret env (expand env args)))
                            :bind
                            (fn [env args]
                              (bind env (expand env args))))))})

      ;; binder
      (tree/put '[binder]
                {:bind
                 (fn [env [argv return]]
                   (let [f (interpret env (list 'fn argv return))]
                     (assoc env
                            :interpret (comp evaluate f)
                            :bind f)))})

      ;; quote
      (tree/put '[quote]
                {:interpret
                 (fn [_ [x]] x)

                 :bind
                 (fn [env [x]] (assoc env :value (list 'quote x)))})

      (tree/put '[qt]
                {:interpret
                 (fn [env [content]]
                   (interpret env (quote/quote-fn 0 content)))

                 :bind
                 (fn [env [content]]
                   (bind env (quote/quote-fn 0 content)))})

      ;; control
      (tree/put '[if]
                {:interpret
                 (fn [env [test then else]]
                   (if (interpret env test)
                     (interpret env then)
                     (interpret env else)))

                 :bind
                 (fn [env [test then else]]
                   (-> (bind env 0 test 1 then 2 else)
                       (assoc :if (list 'if test then else)
                              :build
                              (fn [env]
                                (->> (sequential-children env)
                                     (map build)
                                     (cons 'if))))))})

      (tree/put '[?]
                {:interpret
                 ()
                 :bind
                 (fn [env args]
                   (bind env (control/emit-form args)))})

      ;; collections
      (tree/put '[vector]
                {:interpret
                 (fn [env xs]
                   (mapv (partial interpret env) xs))

                 :bind
                 (fn [env xs]
                   (if (composite/composed? xs)
                     (bind env (composite/expand-vec xs))
                     (-> (reduce (fn [e [i v]] (bind e [i] v))
                                 (assoc env :vector true)
                                 (map-indexed vector xs))
                         (assoc :build
                                (fn [env]
                                  (->> (sequential-children env)
                                       (mapv build)))))))})

      (tree/put '[map-entry]
                {:interpret
                 (fn [env [k v]]
                   (u/map-entry (interpret env k) (interpret env v)))

                 :bind
                 (fn [env [k v]]
                   (bind (assoc env :map-entry true)
                         0 k 1 v))})

      (tree/put '[hash-map]
                {:interpret
                 (fn [env xs]
                   (into {} (map (fn [entry] (mapv (partial interpret env) entry)) xs)))

                 :bind
                 (fn [env xs]
                   (let [hm (into {} xs)]
                     (if (composite/composed? hm)
                       (bind env (composite/expand-map hm))
                       (-> (reduce (fn [e [i [k v]]] (bind e i (list 'map-entry k v)))
                                   (assoc env :hash-map true)
                                   (map-indexed vector xs))
                           (assoc
                            :build
                            (fn [env]
                              (->> (sequential-children env)
                                   (map (fn [e] (mapv build (sequential-children e))))
                                   (into {}))))))))})

      ;; multi functions
      (tree/put '[multi-fn simple]
                {:interpret
                 (fn [_ _]
                   (u/throw [:multi-fn.simple.evalutate :not-implemented]))

                 :bind
                 (fn [env [argv & cases]]
                   (let [predicates (take-nth 2 cases)
                         implementations (map (partial list 'fn argv) (take-nth 2 (next cases)))]
                     (reduce (fn [e [idx impl]] (bind e idx impl))
                             (assoc env
                                    :multi-fn true
                                    :predicates predicates
                                    :bind (fn [env2 args]
                                            (let [returned-env (bind env2 (cons :implementation-placeholder args))
                                                  subenvs (next (sequential-children returned-env))
                                                  arg-check (fn [check arg] (or (= '_ check) (check arg)))
                                                  match? (fn [preds subenvs] (every? identity (map arg-check preds subenvs)))]
                                              (loop [candidates (map-indexed vector predicates)]
                                                (if-let [[[idx pred] & cs] (seq candidates)]
                                                  (if (match? pred subenvs)
                                                    (assoc-in returned-env [::tree/node 0]
                                                              {:link (conj (tree/position env) idx)})
                                                    (recur cs))
                                                  (u/throw [:multi-fn.simple :no-dispatch args]))))))
                             (map-indexed vector implementations))))})))

(defn bind-prog
  [body]
  (if (even? (count body))
    (u/throw [::prog "no return expression." (cons `prog body)])
    (let [[pairs return] (pairs&return body)
          return-symbol (gensym "ret_")
          bindings (conj (vec pairs) [return-symbol return])
          bound (reduce (fn [e [s v]] (bind e s v)) ENV0 bindings)]
      (cd bound return-symbol))))

(defmacro prog
  [& body]
  (compile (bind-prog body)))

(defmacro prog'
  [& body]
  `(bind-prog ~(mapv quote/quote-wrap body)))

(do :tries

    (comment
      (do :bind

          (build (bind ENV0 'x 1 'y 2 '(+ x y))
                 DEFAULT_COMPILER_OPTS)

          (bind ENV0 'f '(fn [a] a))

          (bind ENV0 'ret '(let [a 1] a))

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
                (bind 'ret2 '(fun x ret a))))

          (bind ENV0 'f '(fn [x y] (let [z 5] (- z x y)))))

      (do :interpret
          E1
          (cd E1 '[z 1])
          (interpret E1 'x)
          (interpret E1 'x-link)
          (interpret E1 'z)
          (interpret E1 'ret)
          ((interpret ENV0 '(fn [a] a))
           1)
          (interpret ENV0
                     '((mac [_ args] (list (second args) (first args) (nth args 2)))
                       1 + 2)))

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
              (build DEFAULT_COMPILER_OPTS))))

    (do :progn

        (do :simple


            (transitive-deps
             (prog' x 1 y 2 (+ x y)))

            (compile
             (prog' x 1 y x (+ y y)))

            (prog (let [x 1 y 2] (+ y x)))

            (prog (let [x 1 y 3]
                    (let [z 5]
                      (+ x y z))))

            (prog x 1
                  f (fn [a b] (let [y 4] (+ x y a b)))
                  (f 4 5))

            (prog x 1 y x (+ y y)))

        (do :lambda


            (prog ((fn [a b] (+ a b)) 1 2))
            (prog f (fn [a b] (+ a b)) (f 1 2)))

        (do :mac

            (prog infix (mac [_ args] (clojure.core/list (second args) (first args) (nth args 2)))
                  (infix 1 + 2))

            (prog ((mac [_ args] (clojure.core/list (second args) (first args) (nth args 2)))
                   1 + 2))

            (bind ENV0 'infix '(mac [_ args] (list (second args) (first args) (nth args 2))))

            (bind ENV0 'm '(binder [e _] e))

            (prog this-value 4
                  m (binder [e args]
                            (bind e (qt (let [this ~this-value] ~(first args)))))
                  (m (list this))))

        (do :quote

            (prog 'io)
            (prog ((mac [_ args] (list '+ (first args) (second args))) 1 2)))

        (do :if

            (prog (if true :ok :ko))
            (prog (if (= 1 ((fn [a] a) 2))
                    (let [x 1 y 2] (+ x y))
                    'ko)))

        (do :recursion

            (bind ENV0 'f '(fn [x] (if (pos? x) (f (dec x)) :done)))
            (prog f (fn [x] (if (pos? x) (f (dec x)) :done))
                  (f 10)))

        (do :collection
            (prog x 1 y 2 [x y])
            (prog x 1 y :foo {y x})
            (prog xs (range 3)
                  [:op . xs])
            (prog x 1 y :foo z {y x}
                  {:a 3 . z}))

        (do :multi-fn
            (prog mf (multi-fn.simple [x y]
                                      [:number :number] (+ x y)
                                      [:string :string] (str x y))
                  n (mf 1 2)
                  s (mf "io " "gro.")
                  [n s]))

        (do :destructure
            (prog (let [[x . xs] (range 10)]
                    [x xs]))

            (prog (let [{:a a . m} {:a 1 :b 2 :c 3}]
                    [a m]))

            (prog f (fn [x [a b c]] (+ x a b c))
                  (f 1 [2 3 4])))

        (do :modules

            (prog math (module add (fn [x y] (+ x y))
                               sub (fn [x y] (- x y)))
                  (math.add 1 2))

            (prog num (module [x]
                              add (fn [y] (+ x y))
                              sub (fn [y] (- x y)))
                  one (num 1)
                  (one.add 4)))

        (do :unquote
            (bind ENV0 'x '~(+ 1 2))
            (prog x ~(+ 1 2)
                  x))

        (do :control

            (bind ENV0 'x '(? (pos? 1) :ok :ko))
            (prog (? (pos? 1) :ok :ko)))))
