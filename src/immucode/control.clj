(ns immucode.control
  (:require [immucode.destructure :as destructure]
            [immucode.utils :as u]
            [clojure.string :as str]))

(def DEFAULT_OPTIONS
  {:bind (fn [a b c] (if (= a b) c (list 'let [a b] c)))
   :check identity
   :throw (fn [e] (list `u/throw e))})

(defn options [& {:as m}]
  (let [{:as opts :keys [check branch]}
        (merge DEFAULT_OPTIONS (eval m))]
    (assoc opts
           :branch (or branch
                       (fn [p t e]
                         (list 'if (check p) t e))))))

(defn pairs&return [xs]
  (if (odd? (count xs))
    [(partition 2 (butlast xs)) (last xs)]
    [(partition 2 xs) nil]))

(defn options&body [[x & xs]]
  (if (map? x)
    [(options x) xs]
    [(options) (cons x xs)]))

;; thunk : lambda of zero argument
;; TODO use thunks only when needed (better performances)

(defn- thunk-symbols
  "generating symbols to hold case thunks"
  ([] (map #(gensym (str "case_" % "_")) (range))))

(defn- compile-case
  [{:as   this
    :keys [test bindings return next]}
   {:as options
    :keys [branch bind throw default]}]
  (let [skip (if next (list next) default)]
    (cond
      test (branch test return skip)
      bindings (let [[b1 b2 & bs] bindings
                     return (compile-case (assoc this :bindings bs) options)]

                 (case (:mode (meta b1)
                              :short-circuiting)

                   :optional
                   (bind b1 b2 return)

                   :short-circuiting
                   (bind b1 b2
                         (branch b1 return skip))

                   :strict
                   (bind b1 b2
                         (branch b1 return
                                 (throw [::strict-binding [b1 b2]])))))
      :else return)))

(defn- cases->thunks
  [cases options]
  (mapv (fn [case]
          [(:symbol case) (list 'fn [] (compile-case case options))])
        cases))

(defn- parse
  [body]
  (let [[pairs return] (pairs&return body)]
    (conj (vec pairs) [::bottom return])))

(defn- body->cases
  [body options]
  (mapv (fn [[left right] [sym nxt]]
          (let [bindings? (vector? left)
                bottom? (= ::bottom left)]
            {:return   right
             :symbol   sym
             :next     (when-not bottom? nxt)
             :test     (if-not (or bindings? bottom?) left)
             :bindings (when bindings? (destructure/bindings left options))}))
        (parse body)
        (partition 2 1 (thunk-symbols))))

(defn emit-form
  ([body]
   (emit-form body (options)))
  ([body options]
   (let [cases (body->cases body options)
         return (compile-case (first cases) options)]
     (if (next cases)
       (let [bindings (->> (cases->thunks (next cases) options)
                           reverse (mapcat identity) vec)]
         (list 'let bindings return))
       return))))

(defmacro ?
  ""
  [& xs]
  (let [[options body] (options&body xs)]
       (emit-form body options)))



(defn emit-OR [body {:keys [branch bind]}]
  (reduce (fn [a e]
            (if (symbol? e)
              (branch e e a)
              (let [s (gensym)]
                (bind s e (branch s s a)))))
          (reverse body)))

(defn emit-AND [body {:keys [branch default]}]
  (reduce (fn [a e] (branch e a default))
          (reverse body)))

(defmacro OR [& xs]
  (let [[options body] (options&body xs)]
    (emit-OR body options)))

(defmacro AND [& xs]
  (let [[options body] (options&body xs)]
    (emit-AND body options)))






(do :extras

    (defmacro ^:private error
      "handle error throwing for the `!` macro"
      [& xs]
      `(throw (new ~(if (:ns &env) 'js/Error 'Exception)
                   ~(str/join "\n" xs))))

    (defmacro !
      "Like `?` but has to return something truthy.
       Otherwise an error is thrown with the value of the optional last expression"
      [& body]
      (case (count body)
        1 `(or ~(first body) (error "is not !" '~(first body)))
        2 `(or ~(first body) (error ~(second body)))
        (let [[cases error-data]
              (if (even? (count body))
                [(butlast body) (last body)]
                [body nil])
              body (mapcat (fn [[left right]] [left (if error-data `(! ~right ~error-data) `(! ~right))])
                           (partition 2 cases))]
          `(? ~@body))))



    (defmacro f?
      "The lambda version of `?`
       A multi case function"
      [& xs]
      (let [[name & xs] (? (symbol? (first xs)) xs (cons nil xs))
            [doc & body] (? (string? (first xs)) xs (cons nil xs))
            arity-map (group-by (comp count first) (partition 2 body))]
        `(fn
           ~@(when name [name])
           ~@(when doc [doc])
           ~@(map (fn [[arity cases]]
                    (let [argv (mapv #(gensym (str "arg_" % "_")) (range arity))]
                      (list argv (cons `? (mapcat (fn [[pat ret]] [(vec (interleave pat argv)) ret])
                                                  cases)))))
                  arity-map))))

    )

(comment :scratch

         (macroexpand-1 '(or a b c))
         (macroexpand-1 '(OR a (b o n) c))
         (macroexpand-1 '(AND {:check (partial list 'test)}
                              (e x p) b c))

         (macroexpand-1 '(? (pos? 1) :ok))

         (macroexpand-1 '(? [a (get m :a)]
                            (+ a a)
                            :fail))

         (macroexpand-1 '(? (pos? x) [:pos x]
                            (neg? x) [:neg x]
                            :zero))

         (defmacro bench [x n]
           `(let [now# (System/currentTimeMillis)]
              (dotimes [_# ~n] ~x)
              (- (System/currentTimeMillis) now#)))

         (letfn [(f [x]
                   (? (pos? x) [:pos x]
                      (neg? x) [:neg x]
                      :zero))
                 (g [x]
                   (cond (pos? x) [:pos x]
                         (neg? x) [:neg x]
                         :else :zero))]

           [(bench (mapv g [-1 0 1]) 10000000)
            (bench (mapv f [-1 0 1]) 10000000)
            ])

         (? [?a nil] :ok)
         (? [!a nil] :ok)

         (? [(ks a b) {:a 1 :b 4}]
            [a b])


         (? [(ks ?a b) {:b 4}]
            [a b])



         )
