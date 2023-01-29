(ns immucode.control
  (:require [immucode.destructure :as destructure]
            [immucode.utils :as u]
            [clojure.string :as str]))

;; thunk : lambda of zero argument

(defn- thunk-symbols
  "generating symbols to hold case thunks"
  ([] (map #(gensym (str "case_" % "_")) (range))))

(defn- compile-case
  [{:as   case'
    :keys [test bindings return next]}]
  (let [cont (when next (list next))]
    (cond
      test `(if ~test ~return ~cont)
      bindings (let [[b1 b2 & bs] bindings]
                 (case (:mode (meta b1)
                              :short-circuiting)

                   :optional
                   `(let [~b1 ~b2]
                      ~(compile-case (assoc case' :bindings bs)))

                   :short-circuiting
                   `(if-let [~b1 ~b2]
                      ~(compile-case (assoc case' :bindings bs))
                      ~cont)

                   :strict
                   `(if-let [~b1 ~b2]
                      ~(compile-case (assoc case' :bindings bs))
                      (u/throw [::strict-binding ['~b1 '~b2]]))))
      :else return)))

(defn- cases->thunks
  [cases]
  (mapv (fn [case]
          (list (:symbol case) [] (compile-case case)))
        cases))

(defn- normalize-body
  [body]
  (if (odd? (count body))
    (concat (butlast body) [::bottom (last body)])
    (concat body [::bottom nil])))

(defn- body->cases
  [body]
  (mapv (fn [[left right] [sym nxt]]
          (let [bindings? (vector? left)
                bottom? (= ::bottom left)]
            {:return   right
             :symbol   sym
             :next     (when-not bottom? nxt)
             :test     (if-not (or bindings? bottom?) left)
             :bindings (when bindings? (destructure/bindings left {}))}))
        (partition 2 (normalize-body body))
        (partition 2 1 (thunk-symbols))))

(defn- emit-form
  [body]
  (let [thunks (-> (body->cases body) cases->thunks)
        return (nth (first thunks) 2)]
    (if-let [bindings (some-> (next thunks) vec)]
      `(letfn ~(reverse bindings) ~return)
      return)))

(defmacro ?
  ""
  [& body]
  (emit-form body))



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



    (defmacro §
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