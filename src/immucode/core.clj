(ns immucode.core
  (:require [immucode.path :as path]
            [immucode.tree :as tree]
            [immucode.utils :as u :refer [cp]]
            [clojure.string :as str]))

(do :one

    (declare evaluate)

    (defn eval-symbol
      [env sym]
      (if-let [found (tree/find env (path/path sym))]
        (:value found)
        (if-let [resolved (resolve sym)]
          (deref resolved)
          (u/throw [:unresolvable sym :in env]))))

    (defn eval-list
      [env [verb & args]]
      (apply (evaluate env verb)
             (map (partial evaluate env) args)))

    (defn evaluate
      [env expr]
      (cp expr
          symbol? (eval-symbol env expr)
          seq? (eval-list env expr)
          coll? (u/$ expr (partial evaluate env))
          expr))

    (defonce evaluate-memoized
      (memoize evaluate))

    (defn define
      [env sym expr]
      (let [path (path/path sym)]
        (tree/upd (tree/ensure-path env path)
                  path
                  (fn [subenv]
                    (assoc subenv :value (evaluate-memoized subenv expr))))))

    (defn cd [env sym]
      (tree/cd env (path/path sym)))

    (def ENV0 {})

    (defmacro program [& forms]
      `(-> ENV0
           ~@(map (fn [[verb & args]]
                    (cons verb (map u/quote-wrap args)))
                  forms)))

    (let [e1
          (-> ENV0
              (define 'foo 42)
              (define 'user.x '(+ foo foo))
              (cd 'user)
              (define 'y.z '(+ x x))
              (define 'ret '(+ x y.z))
              (cd 'ret))
          e2
          (program
           (define foo 42)
           (define user.x (+ foo foo))
           (cd user)
           (define y.z (+ x x))
           (define ret (+ x y.z))
           (cd ret))]
      (assert (and (= e1 e2)
                   (= 252 (:value e1))))))

[:todo
 "track-dependencies => optimized compilation"
 "capture evaluation env on each subnode"
 "laziness, value is computed only on need"]

(do :two

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

        (defn expression-subenvs [env]
          (assert (:expression env))
          (map (fn [idx] (tree/cd env [idx]))
               (range (count (:expression env))))))

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

           seq? (let [verb (bubfind env (first expr))]
                  (if-let [f (:evaluate verb)]
                    (f env (rest expr))
                    (let [[verb & args]
                          (map (partial evaluate env) expr)]
                      (apply verb args))))

           expr))

      ([env at expr]
       (evaluate (cd env at) expr)))

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

           seq? (let [verb (bubfind env (first expr))]
                  (if-let [f (:bind verb)]
                    (f env (rest expr))
                    (reduce (fn [env [idx subexpr]]
                              (bind env idx subexpr))
                            (assoc env :expression expr)
                            (map-indexed vector expr))))

           (assoc env :value expr)))

      ([env sym expr]
       (let [path (path/path sym)]
         (if (tree/cd env path)
           (u/throw [::bind "already defined path" sym env])
           (tree/upd (tree/ensure-path env path)
                     path
                     #(bind % expr))))))

    (def ENV0

      (-> {}
          ;; lambda
          (tree/put '[fn] {:evaluate
                          (fn [env [argv return]]
                            (fn [& xs]
                              (let [env+ (reduce (fn [e [argsym argval]]
                                                   (tree/put e [argsym] :value argval))
                                                 env (zipmap argv (map (partial evaluate env) xs)))]
                                (evaluate env+ return))))

                          :bind
                          (fn [env [argv return]]
                            (let [retsym (gensym "ret_")
                                  return-path (conj (tree/position env) retsym)
                                  form (list 'fn argv return)]
                              (bind (reduce (fn [e a]
                                              (tree/put e [a] :local a))
                                            (assoc env
                                                   :lambda form
                                                   :argv argv
                                                   :return return-path)
                                            argv)
                                    retsym
                                    return)))})
          ;; let
          (tree/put '[let] {:evaluate
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
                                    return))})))

    (do :bind
        (-> ENV0
            (bind 'fun '(fn [a] a))
            (bind 'ret '(fun 1 2))
            (cd 'ret)
            (compile))

        (-> ENV0
            (bind 'ret '(let [a 1 b 2] (+ a b)))
            (cd 'ret)
            (compile))

        (-> ENV0
            (bind 'f '(fn [x] (let [a 1 b 2] (+ x a b))))
            (bind 'ret '(f 1))
            (cd 'ret)
            (compile))

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

    (do :evaluate
        E1
        (cd E1 '[z 1])
        (evaluate E1 'x)
        (evaluate E1 'x-link)
        (evaluate E1 'z)
        (evaluate E1 'ret)
        ((evaluate ENV0 '(fn [a] a))
         1))

    (defn deps
      [{:as env :keys [lambda link expression]}]
      (cond
        link (append1 (deps (tree/at env link)) link)
        lambda (deps (tree/at env (:return env)))
        expression (reduce
                    (fn [ds subenv]
                      (let [ds+ (deps subenv)]
                        (concat ds+ (remove (set ds+) ds))))
                    () (expression-subenvs env))))

    (do :deps
        (deps (cd E1 'ret))
        (deps (cd E1 'ret2)))

    (comment :useless?

             (defn remove-duplicates [xs]
               (loop [seen #{} todo xs ret []]
                 (if-let [[x & xs] (seq todo)]
                   (if (seen x)
                     (recur seen xs ret)
                     (recur (conj seen x) xs (conj ret x)))
                   (seq ret))))

             (defn undup-stack-conj [q x]
               (cons x (remove (partial = x) q)))

             (defn exploration
               [seen {:as env :keys [local value link expression]}]
               (cond local seen
                     value seen
                     link (exploration (undup-stack-conj seen link) (tree/at env link))
                     expression (expression-subenvs env))))

    (defn compile1
      [{:as env :keys [lambda local link expression value var]}]
      (or value
          local
          (cond
            var (var->qualified-symbol var)
            link (path->var-sym link)
            lambda `(fn ~(:argv env) ~(compile1 (tree/at env (:return env))))
            expression (map compile1 (expression-subenvs env)))))

    (defn compile
      ([env {:keys [bind-return-compiler]}]
       (bind-return-compiler
        (->> (deps env)
             (map (partial tree/at env))
             (map (juxt env->var-sym compile1)))
        (compile1 env)))
      ([env]
       (compile env {:bind-return-compiler
                     (fn [bindings return]
                       `(let ~(vec (mapcat identity bindings)) ~return))})))

    (do :compile
        (compile (cd E1 'ret))
        (eval (compile (cd E1 'ret2))))



    )
