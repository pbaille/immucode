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
          (symbol (str/join "_" p)))

        (defn var->qualified-symbol [v]
          (let [{:keys [ns name]} (meta v)]
            (symbol (str ns) (str name)))))

    (defn bind

      ([env expr]
       (cp expr
           symbol? (if-let [found (tree/find env (path/path expr))]
                     (assoc env :link found)
                     (if-let [resolved (resolve expr)]
                       (assoc env :value (deref resolved))
                       (u/throw [:unresolvable expr :in env])))

           seq? (let [[verb & args] (mapv (partial bind env) expr)]
                  (assoc env
                         :expression
                         {:verb verb :args args}))

           (assoc env :value expr)))

      ([env sym expr]
       (let [path (path/path sym)]
         (tree/upd (tree/ensure-path env path)
                   path
                   #(bind % expr)))))

    (defn evaluate
      ([{:as env :keys [link expression code value]}]
       (cond
         value value
         link (evaluate link)
         expression (apply (evaluate (:verb expression))
                           (map evaluate (:args expression)))))
      ([env at]
       (evaluate (cd env at))))

    (defn env->var-sym [env]
      (path->var-sym (tree/position env)))

    (defn compile
      [{:as env :keys [link expression code value]}]
      (cond
        value value
        link (compile link)
        expression (cons (compile (:verb expression))
                         (map compile (:args expression)))))

    (do :assertions

        (bind {} 3)
        (bind {} '(+ 1 2 (- 3 4)))

        (-> ENV0
            (bind 'x 1)
            (bind 'y 'x)
            (bind 'z '(+ x y)))

        (def E1
          (-> ENV0
              (bind 'x 1)
              (bind 'y 2)
              (bind 'a 34)
              (bind 'z '(+ x y))
              (bind 'ret '(+ z z))))

        (assert (= 6 (evaluate E1 'ret)))

        (compile (cd E1 'ret))
        #_(assert
           (do (eval (compile (cd E1 'ret)))
               (= ret 6))))

    )
