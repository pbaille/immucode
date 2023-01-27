(ns immucode.core
  (:require [immucode.path :as path]
            [immucode.tree :as tree]
            [immucode.utils :as u :refer [cp]]
            [immucode.composite-literals :as composite]
            [immucode.destructure :as destructure]
            [immucode.quote :as quote]
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
      (if (and (symbol? x)
               (not (namespace x)))
        (tree/find env (path/path x))))

    (defn env-get [env at]
      (tree/cd (tree/root env) (path/path at)))

    (defn indexed-subenvs
      [{:as env :keys [indexed]}]
      (assert indexed
              (str [::expression-subenvs :not-indexed]))
      (map (fn [idx] (tree/cd env [idx]))
           (range indexed)))

    (defn resolve-key [env k]
      (if env
        (or (get env k)
            (if-let [link (:link env)]
              (resolve-key (tree/at env link) k)))))

    (defn pairs&return [xs]
      (if (odd? (count xs))
        [(partition 2 (butlast xs)) (last xs)]
        [(partition 2 xs) nil])))

(defn bind

  "Load some expressions into the given environment"

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
              (if (composite/composed? expr)
                (bind env (composite/expand-seq expr))
                (reduce (fn [env [idx subexpr]]
                          (bind env idx subexpr))
                        (assoc env
                               :expression expr
                               :indexed (count expr))
                        (map-indexed vector expr))))

       vector? (bind env (cons 'vector expr))

       map? (bind env (cons 'hash-map expr))

       (let [type (u/simple-type expr)]
         (assoc env
                :value expr
                type true
                :type type))))

  ([env sym expr]
   (let [path (path/path sym)]
     (if (tree/cd env path)
       (u/throw [::bind "already defined path" sym env])
       (tree/upd (tree/ensure-path env path)
                 path
                 #(bind % expr)))))

  ([env sym expr & more]
   (let [[bindings return] (pairs&return (list* sym expr more))]
     (-> (reduce (fn [env [sym expr]] (bind env sym expr))
                 env bindings)
         (bind return)))))

(defn evaluate

  ([{:as env :keys [expression link var value]}]
   (or value
       (if-let [f (:evaluate env)] (f env))
       (cond
         var (deref var)
         link (evaluate (tree/at env link))
         expression (let [[verb & args]
                          (map evaluate
                               (indexed-subenvs env))]
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
              (if (composite/composed? expr)
                (evaluate env (composite/expand-seq expr))
                (let [[verb & args]
                      (map (partial evaluate env) expr)]
                  (apply verb args))))

       vector? (evaluate env (cons 'vector expr))

       map? (evaluate env (cons 'hash-map expr))

       expr))

  ([env at expr]
   (evaluate (cd env at) expr)))

(def DEFAULT_COMPILER_OPTS
  {:global-bind-return (fn [bindings return] (if (seq bindings) `(do ~@(map (fn [[sym val]] (list 'def sym val)) bindings) ~return) return))
   :local-bind-return (fn [bindings return] (if (seq bindings) `(let ~(vec (mapcat identity bindings)) ~return) return))
   :lambda-compiler (fn [name argv return] `(fn ~@(if (symbol? name) [name]) ~argv ~return))
   :branch-compiler (fn [test then else] (list 'if test then else))
   :application-compiler (fn [& xs] (list* xs))
   :external-symbol-compiler var->qualified-symbol
   :binding-symbol-compiler path->var-sym})

(defn deps
  [{:as env :keys [link return indexed]}]
  (cond
    link (append1 (deps (tree/at env link)) link)
    return (remove (partial path/parent-of (tree/position env))
                   (deps (tree/at env return)))
    indexed
    (reduce
     (fn [ds subenv]
       (let [ds+ (deps subenv)]
         (concat ds+ (remove (set ds+) ds))))
     () (indexed-subenvs env))))

(defn build

  "emit executable code evaluating to the value of the current node of the environment"

  [env
   {:as options
    :keys [global-bind-return local-bind-return
           external-symbol-compiler binding-symbol-compiler
           application-compiler lambda-compiler branch-compiler
           captures]}]

  (let [deps (remove (set captures) (deps env))]

    (letfn [(build1 [{:as env
                      :keys [local var value link branch expression vector hash-map return]}]
              (cond

                ;; external var
                var (external-symbol-compiler var)

                ;; environment path
                link (binding-symbol-compiler link)

                ;; application
                expression (apply application-compiler (map build1 (indexed-subenvs env)))

                ;; if
                branch (apply branch-compiler (map build1 (indexed-subenvs env)))

                ;; collections
                vector (mapv build1 (indexed-subenvs env))
                hash-map (into {} (map (fn [e] [(build1 (tree/cd e '[0])) (build1 (tree/cd e '[1]))])
                                       (indexed-subenvs env)))

                ;; let and lambda
                return (let [subbuild (build (tree/at env (:return env))
                                             (assoc options
                                                    :captures deps
                                                    :binding-symbol-compiler
                                                    (fn [p] (binding-symbol-compiler (or (path/remove-prefix p (:return env)) p)))))]
                         (if (:lambda env)
                           (lambda-compiler (:name env) (:argv env) subbuild)
                           subbuild))

                ;; value or locally bound symbol
                :else (or local value)))]

      (let [bindings
            (map (juxt binding-symbol-compiler
                       (comp build1 (partial tree/at env)))
                 deps)]

        (if (tree/root? env)
          (global-bind-return bindings (build1 env))
          (local-bind-return bindings (build1 env)))))))

(def ENV0

  (-> {}
      ;; let
      (tree/put '[let]
                {:evaluate
                 (fn [env [bindings return]]
                   (-> (reduce (fn [e [argsym argval]]
                                 (tree/put e [argsym] :value (evaluate e argval)))
                               env (partition 2 (destructure/bindings bindings {})))
                       (evaluate return)))

                 :bind
                 (fn [env [bindings return]]

                   (let [return-symbol '__return__

                         return-path
                         (conj (tree/position env) return-symbol)

                         initial
                         (assoc env
                                :form (list 'let bindings return)
                                :local-scope true
                                :return return-path)

                         with-bindings
                         (reduce (fn [e [sym expr]]
                                   (bind e sym expr))
                                 initial
                                 (partition 2 (destructure/bindings bindings {})))]

                     (bind with-bindings
                           return-symbol
                           return)))})
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

                         initial
                         (assoc env
                                :lambda form
                                :name fn-name
                                :argv argument-symbols
                                :return return-path)

                         with-locals
                         (reduce (fn [e a]
                                   (tree/put e [a] :local a))
                                 initial
                                 (cons fn-name argument-symbols))

                         destructuration-bindings
                         (mapcat (juxt :destructure :symbol)
                                 (filter :destructure arguments))

                         return-expression
                         (if (seq destructuration-bindings)
                           (list 'let destructuration-bindings return)
                           return)]

                     (bind with-locals
                           return-symbol
                           return-expression)))})

      ;; mac
      (tree/put '[mac]
                {:bind
                 (fn [env [argv return]]
                   (let [expand (evaluate env (list 'fn argv return))]
                     (assoc env
                            :evaluate
                            (fn [env args]
                              (evaluate env (expand env args)))
                            :bind
                            (fn [env args]
                              (bind env (expand env args))))))})

      ;; binder
      (tree/put '[binder]
                {:bind
                 (fn [env [argv return]]
                   (assoc env :bind (evaluate env (list 'fn argv return))))})

      ;; quote
      (tree/put '[quote]
                {:evaluate
                 (fn [_ [x]] x)

                 :bind
                 (fn [env [x]] (assoc env :value (list 'quote x)))})

      ;; if
      (tree/put '[if]
                {:evaluate
                 (fn [env [test then else]]
                   (if (evaluate env test)
                     (evaluate env then)
                     (evaluate env else)))

                 :bind
                 (fn [env [test then else]]
                   (bind (assoc env
                                :branch (list 'if test then else)
                                :indexed 3)
                         0 test
                         1 then
                         2 else))})

      ;; collections
      (tree/put '[vector]
                {:evaluate
                 (fn [env xs]
                   (mapv (partial evaluate env) xs))

                 :bind
                 (fn [env xs]
                   (if (composite/composed? xs)
                     (bind env (composite/expand-vec xs))
                     (reduce (fn [e [i v]] (bind e [i] v))
                             (assoc env :vector true :indexed (count xs))
                             (map-indexed vector xs))))})

      (tree/put '[map-entry]
                {:evaluate
                 (fn [env [k v]]
                   (u/map-entry (evaluate env k) (evaluate env v)))

                 :bind
                 (fn [env [k v]]
                   (bind (assoc env :indexed 2 :map-entry true)
                         0 k 1 v))})

      (tree/put '[hash-map]
                {:evaluate
                 (fn [env xs]
                   (into {} (map (fn [entry] (mapv (partial evaluate env) entry)) xs)))

                 :bind
                 (fn [env xs]
                   (let [hm (into {} xs)]
                     (if (composite/composed? hm)
                       (bind env (composite/expand-map hm))
                       (reduce (fn [e [i [k v]]] (bind e i (list 'map-entry k v)))
                               (assoc env :hash-map true :indexed (count xs))
                               (map-indexed vector xs)))))})

      ;; multi functions
      (tree/put '[multi-fn simple]
                {:evaluate
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
                                                  subenvs (next (indexed-subenvs returned-env))]
                                              (loop [candidates (map-indexed vector predicates)]
                                                (if-let [[[idx pred] & cs] (seq candidates)]
                                                  (if (every? identity (map #(%1 %2) pred subenvs))
                                                    (assoc-in returned-env [:node 0]
                                                              {:link (conj (tree/position env) idx)})
                                                    (recur cs))
                                                  (u/throw [:multi-fn.simple :no-dispatch args]))))))
                             (map-indexed vector implementations))))})

      (tree/put '[qt]
                {:evaluate
                 (fn [_ _] (u/throw [:sub.evaluate :not-implemented]))

                 :bind
                 (fn [env [content]]
                   (bind env (quote/quote-fn 0 content)))})))

(defmacro progn
  "Takes a flat series of bindings followed or not by a return value.
   Build the corresponding program using default options."
  [& xs]
  (-> (apply bind ENV0 xs)
      (build DEFAULT_COMPILER_OPTS)))





(do :tries

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

        (do :simple

            (progn x 1 y 2 (+ x y))

            (progn (let [x 1 y 2] (+ y x)))

            (progn (let [x 1 y 3]
                     (let [z 5]
                       (+ x y z))))

            (progn x 1
                   f (fn [a b] (let [y 4] (+ x y a b)))
                   (f 4 5))

            (progn x 1 y x (+ y y)))

        (do :lambda

            (progn ((fn [a b] (+ a b)) 1 2)))

        (do :nested-bindings

            #_(progn x 1
                     y (let [z 3] (+ x z))
                     (+ y.z x y)))

        (do :mac

            (progn infix (mac [_ args] (list (second args) (first args) (nth args 2)))
                   (infix 1 + 2))

            (progn ((mac [_ args] (list (second args) (first args) (nth args 2)))
                    1 + 2))

            (bind ENV0 'infix '(mac [_ args] (list (second args) (first args) (nth args 2))))

            (bind ENV0 'm '(binder [e _] e))

            (progn this-value 4
                   m (binder [e args] (bind
                                       (bind
                                        (bind e 'this this-value)
                                        'return (first args))
                                       'return))
                   (m (list this)))

            (progn this-value 4
                   m (binder [e args] (bind
                                       (bind e 'this this-value)
                                       (first args)))
                   (m (list this)))

            #_ (progn m (mac [e args] (build
                                       (bind (bind e 'this :this)
                                             (first args))
                                       DEFAULT_COMPILER_OPTS))
                      (m this)))

        (do :quote

            (progn 'io)
            (progn ((mac [_ args] (list '+ (first args) (second args))) 1 2)))

        (do :if

            (progn (if true :ok :ko))
            (progn (if (= 1 ((fn [a] a) 2))
                     (let [x 1 y 2] (+ x y))
                     'ko)))

        (do :recursion

            (bind ENV0 'f '(fn [x] (if (pos? x) (f (dec x)) :done)))
            (progn f (fn [x] (if (pos? x) (f (dec x)) :done))
                   (f 10)))

        (do :collection
            (progn x 1 y 2 [x y])
            (progn x 1 y :foo {y x})
            (progn xs (range 3)
                   [:op . xs])
            (progn x 1 y :foo z {y x}
                   {:a 3 . z}))

        (do :multi-fn
            (progn mf (multi-fn.simple [x y]
                                       [:number :number] (+ x y)
                                       [:string :string] (str x y))
                   n (mf 1 2)
                   s (mf "io " "gro.")
                   [n s]))

        (do :destructure
            (progn (let [[x . xs] (range 10)]
                     [x xs]))

            (progn (let [{:a a . m} {:a 1 :b 2 :c 3}]
                     [a m]))

            (progn f (fn [x [a b c]] (+ x a b c))
                   (f 1 [2 3 4])))))
