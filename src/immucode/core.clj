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

        (defn add-deps [env x]
          (cp x
              nil? env
              path/path? (update env :deps (fnil conj #{}) x)
              set? (update env :deps (fnil into #{}) x)
              (u/throw [:add-deps/bad-input x])))

        (defn deps-seq [env]
          (if-let [deps (seq (:deps env))]
            (concat (mapcat (fn [at] (deps-seq (tree/find env at))) deps) deps)
            []))

        (deps-seq (tree/cd E1 ['ret]))

        (defn path->var-sym [p]
          (symbol (str/join "_" p))))

    (do :bind

        (declare bind)

        (defn bind-symbol
          [env sym]
          (let [target (path/path sym)
                found (tree/find env target)]
            (if found
              (let [path (tree/position found)]
                (-> (assoc env :link path)
                    (add-deps path)))
              (if-let [resolved (resolve sym)]
                (assoc env :value (deref resolved))
                (u/throw [:unresolvable sym :in env])))))

        (defn bind-list
          [env expr]
          (reduce
           (fn [e [idx subexpr]]
             (let [subenv (bind env subexpr)]
               (-> (assoc-in e [:application idx] subenv)
                   (add-deps (:deps subenv)))))
           env
           (map-indexed vector expr)))

        (defn bind
          [env expr]
          (let [env (assoc env :code expr)]
            (cp expr
                symbol? (bind-symbol env expr)
                seq? (bind-list env expr)
                env)))

        (def bind-memoized
          (memoize bind))

        (do :tries

            (bind {}
                  '(+ 1 2 (- 3 4)))

            (path/path [])

            (bind {} 3)

            (tree/put {} [] :iop 2)))

    (defn load
      [env sym expr]
      (let [path (path/path sym)]
        (tree/upd (tree/ensure-path env path)
                  path
                  #(bind-memoized % expr))))

    (do :eval

        (declare evaluate)

        (defn evaluate-application
          [application]
          (let [[operator & operands]
                (map val (sort-by key application))]
            (apply (evaluate operator)
                   (map evaluate operands))))

        (defn evaluate
          ([{:as env :keys [link application code value]}]
           (cond
             value value
             link (evaluate (tree/find env link))
             application (evaluate-application application)
             code code))
          ([env at]
           (evaluate (cd env at)))))

    (defn compile
      [env]
      (let [root-env (tree/root env)
            deps (concat (deps-seq env) (list (tree/position env)))]
        `(do ~@(map (fn [at] (list 'def (path->var-sym at) (:code (tree/cd root-env at))))
                    deps))))

    (do :assertions

        (def E1
          (-> ENV0
              (load 'x 1)
              (load 'y 2)
              (load 'a 34)
              (load 'z '(+ x y))
              (load 'ret '(+ z z))))

        (assert (= 6 (evaluate E1 'ret)))

        (assert
         (do (eval (compile (cd E1 'ret)))
             (= ret 6))))

    )
