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

    (def ENV0 {})

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

        (defn env-get [env at]
          (tree/cd (tree/root env) (path/path at)))

        (defn expression-subenvs [env]
          (assert (:expression env))
          (map (fn [idx] (tree/cd env [idx]))
               (range (count (:expression env)))))

        (defn compile1
          [{:as env :keys [link expression value var]}]
          (cond
            var (var->qualified-symbol var)
            value value
            link (path->var-sym link)
            expression (map compile1 (expression-subenvs env)))))

    (defn bind

      ([env expr]
       (cp expr
           symbol? (if-let [found (tree/find env (path/path expr))]
                     (assoc env :link (tree/position found))
                     (if-let [resolved (resolve expr)]
                       (assoc env :var resolved)
                       (u/throw [:unresolvable expr :in env])))

           seq? (reduce  (fn [env [idx subexpr]]
                           (bind env idx subexpr))
                         (assoc env :expression expr)
                         (map-indexed vector expr))

           (assoc env :value expr)))

      ([env sym expr]
       (let [path (path/path sym)]
         (if (tree/cd env path)
           (u/throw "already defined path " sym env)
           (tree/upd (tree/ensure-path env path)
                     path
                     #(bind % expr))))))

    (do :bind
        (def E1
          (-> ENV0
              (bind 'x 1)
              (bind 'x-link 'x)
              (bind 'y 2)
              (bind 'a 34)
              (bind 'z '(+ x y))
              (bind 'ret '(+ z z)))))

    (defn evaluate
      ([{:as env :keys [link expression value var]}]
       (cond
         var (deref var)
         value value
         link (evaluate (tree/at env link))
         expression (let [[verb & args]
                          (map evaluate
                               (expression-subenvs env))]
                      (apply verb args))))
      ([env at]
       (evaluate (cd env at))))

    (do :evaluate
        E1
        (cd E1 '[z 1])
        (evaluate E1 'x)
        (evaluate E1 'x-link)
        (evaluate E1 'z)
        (evaluate E1 'ret))

    (defn deps
      [{:as env :keys [link expression]}]
      (cond
        link (append1 (deps (tree/at env link)) link)
        expression (reduce
                    (fn [ds subenv]
                      (concat (remove (set ds) (deps subenv)) ds))
                    () (expression-subenvs env))))

    (do :deps
        (deps (cd E1 'ret)))

    (defn compile [env at]
      (let [bindings (->> (deps (cd env at))
                          (map (partial tree/at env))
                          (map (fn [env] (list 'def (path->var-sym (tree/position env)) (compile1 env))))
                          (cons 'do))]
        (append1 bindings
                 (compile1 (cd env at)))))

    (do :compile
        (compile E1 'ret))



    )
