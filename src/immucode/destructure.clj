(ns immucode.destructure
  (:require [immucode.utils :as u :refer [cp]]
            [immucode.composite-literals :as composite]))

(declare bindings)

(do :vec

    (defn raw-vec [v seed options]
      (let [cnt (count v)
            symseed? (symbol? seed)]
        (u/with-gensyms
          [vect head tail linecheck size>= size=]
          (let [vect (if symseed? seed vect)]
            (u/concatv
             (when-not symseed? (bindings [vect seed] options))
             (bindings
              [linecheck `(sequential? ~vect)
               head `(take ~cnt ~vect)
               size>= `(= (count ~head) ~cnt)
               tail `(drop ~cnt ~vect)
               size= `(empty? ~tail)]
              options)
             (mapcat
              (fn [e i] (bindings e `(nth ~head ~i) options))
              (seq v) (range)))))))

    (defn composite-vec [v seed options]
      (let [doti (u/indexof v '.)
            cars (take doti v)
            [eli & queue] (drop (inc doti) v)
            qcnt (count queue)
            symseed? (symbol? seed)]
        (u/with-gensyms
          [ysym qsym cdr']
          (let [ysym (if symseed? seed ysym)]
            (u/concatv
             (when-not symseed? (bindings [ysym seed] options))
             (raw-vec cars `(take ~doti ~ysym) options)
             (bindings eli `(drop ~doti ~ysym) options)
             #_(bind.vec.body cars ysym doti)
             (when-not (zero? qcnt)
               (u/concatv
                (bindings [cdr' eli
                           eli `(drop-last ~qcnt ~cdr')
                           qsym `(take-last ~qcnt ~cdr')] options)
                (raw-vec queue qsym options)))))))))

(do :map

    (defn map-keys [x seed options]
      (mapcat
       (fn [[k v]]
         (bindings v `(get ~seed ~k) options))
       x))


    (defn raw-map [x seed options]
      (u/with-gensyms
        [mapcheck seedsym]
        (u/concatv
         (bindings
          [seedsym seed
           mapcheck `(map? ~seedsym)]
          options)
         (map-keys x seedsym options))))

    (defn composite-map [x seed options]
      (let [rs (get x '.)
            m (dissoc x '.)
            ks (keys m)]
        (u/with-gensyms
          [seedsym]
          (u/concatv
           (bindings [seedsym seed] options)
           (map-keys m seedsym options)
           (bindings rs `(dissoc ~seedsym ~@ks) options))))))

(do :sym

    (defn symbol-mode [s default]
      (let [default (or default :short)]
        (condp = (first (name s))
          \¡ default
          \? :opt
          \! :strict
          \_ :short
          default)))

    (defn parse-symbol [x & [options]]
      (let [name (name x)
            prefix (#{\? \! \¡ \_} (first name))]
        {:prefix prefix
         :name (if prefix (or (and (next name) (symbol (subs name 1))) (gensym)) x)
         :mode (symbol-mode x (:binding-mode options))}))

    (defn symbol-form [seed mode]
      (condp = mode
        :short seed
        :opt `(or ~seed nil) ;; TODO this nil prevents us to switch to nil based shortcircuiting (for performances)
        :strict `(or ~seed (u/throw "strict binding failure:\n" (:data ~seed)))))

    (comment
      (bindings '!a 'x {})
      (parse-symbol '!a)
      (subs "!a" 1)
      (bindings 'a 'b {})))

(def operators
  {:&
   (fn [xs seed options]
     (u/with-gensyms
       [seedsym]
       (apply u/concatv
              (bindings [seedsym seed] options)
              (map #(bindings % seedsym options) xs))))

   :ks
   (fn [xs seed options]
     (bindings (zipmap (map (comp keyword :name parse-symbol) xs) xs)
               seed options))

   :ks-req
   (fn [xs seed options]
     (bindings (zipmap (map keyword xs) xs) seed options))

   :ks-opt
   (fn [xs seed options]
     (let [keys (map keyword xs)
           opt-syms (map (fn [k] (symbol (str "?" (name k)))) xs)]
       (bindings (zipmap keys opt-syms) seed options)))

   :ks-or
   (fn [xs seed options]
     (let [keys (take-nth 2 xs)
           or-exprs (map (fn [[k v]] `(or ~k ~v)) (partition 2 xs))]
       (u/concatv
        ((get operators :ks-opt) keys seed options)
        (interleave keys or-exprs))))

   :quote
   (fn [[a] seed options]
     (bindings (gensym "¡") `(= ~seed '~a) options))

   :bind_
   (fn [[p expr] seed options]
     (bindings ['_ seed p expr] options))

   :!
   (fn [[f & [p]] seed options]
     (bindings (or p (gensym)) (list f seed) options))})

(defn bindings
  ([xs options]
   (vec (mapcat (fn [[pat seed]]
                  (bindings pat seed options))
                (partition 2 xs))))

  ([x seed options]

   (cp x
       symbol?
       (let [{:keys [name mode]}
             (parse-symbol x options)]
         [(with-meta name {:mode mode})
          seed #_(symbol-form seed mode)])

       vector?
       (if (composite/single-dotted? x)
         (composite-vec x seed options)
         (raw-vec x seed options))

       map?
       (if (composite/single-dotted? x)
         (composite-map x seed options)
         (raw-map x seed options))

       seq?
       (let [[v & args] x]
         (if-let [k (and (symbol? v) (keyword v))]
           (if-let [op (get operators k)]
             (op args seed options)))))))

(do :compilation

    (defn unified
      "takes a binding vector (like let) , compile it with 'bindings
       then add unification constraints on symbols that occurs multiple times"
      [xs & [options]]
      (loop [ret [] seen #{}
             [a b & nxt] (bindings xs options)]
        (if a
          (if (seen a)
            (recur (u/concatv ret (bindings (gensym) `(= ~a ~b) options)) seen nxt)
            (recur (conj ret a b) (conj seen a) nxt))
          ret)))

    #_(defn optimize
      ([{:as ret :keys [todo bindings env]}]
       (if (not (seq todo))
         ret
         (optimize
           (let [[sym expr & todo] todo]

             (if (and (symbol? expr)
                      ;; is not rebound later
                      (not (contains? (set (take-nth 2 todo)) expr)))

               {:bindings bindings
                :todo todo
                :env (env/substitute env sym expr)}

               {:bindings (vec/cat bindings [sym (exp/expand env expr)])
                :env (env/shadow env sym)
                :todo todo})))))
      ([env bs]
       (optimize {:todo bs :env env :bindings []})))

    #_(defn compile-let-form
      ([{:keys [env return options] bs :bindings}]

       #_(println "compile-let-form " bs return options)
       (let [bs (bindings bs options)
             bs (if (:unified options) (unified bs options) bs)
             {:keys [env bindings]} (optimize env bs)
             return (exp/expand env return)]
         #_(println "ret exp " return)
         #_(pp env)
         (if-not (seq bindings)
           return
           (loop [return return
                  [[p1 e1] & pes :as bs]
                  (reverse (partition 2 bindings))]
             (if-not (seq bs)
               return
               (let [mode (:mode (meta p1))]
                 (recur (condp = mode
                          :opt
                          (if (= p1 return)
                            e1 `(let [~p1 ~e1] ~return))

                          :strict
                          `(let [~p1 ~e1]
                             (if (rug.core/success? ~p1)
                               ~return
                               (e/error "strict binding failure:\n" (:data ~p1))))

                          :short
                          (if (= p1 return)
                            e1 `(let [~p1 ~e1]
                                  (if (rug.core/success? ~p1)
                                    ~return
                                    ~p1))))
                        pes)))))))

      ([env bindings return options]
       (compile-let-form
         {:env env :bindings bindings
          :return return :options options}))))
