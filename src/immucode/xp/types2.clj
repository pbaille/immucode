(ns immucode.xp.types2
  (:refer-clojure :exclude [type boolean float symbol keyword vector-of vector list hash-map hash-set])
  (:require [clojure.core :as c]
            [immucode.utils :as u]))

(do :help

    (defn remove-duplicates [xs]
      (loop [seen #{} return [] todo xs]
        (if-let [[x & xs] (seq todo)]
          (if (contains? seen x)
            (recur seen return xs)
            (recur (conj seen x) (conj return x) xs))
          return))))

(defn type [data proto]
  (vary-meta data
             merge
             {::type true
              ::proto proto}))

(defn type? [x]
  (some-> x meta ::type))

(defn singleton [x]
  (type {:singleton true
         :form [:singleton x]
         :value x}
        {:value-check
         (fn [this v] (= v (:value this)))}))

(defn ->type [x]
  (if (type? x)
    x
    (singleton x)))

(defn proto [x]
  (-> (->type x) meta ::proto))

(defn proto-get [x k]
  (get (proto x) k))

(defn call-method [x k y]
  (if-let [f (proto-get x k)]
    (f x y)
    (u/throw [::call-method ::unfound k x])))

(defn checker [t]
  (let [t (->type t)
        check (:value-check (proto t))]
    (fn [v]
      (check t v))))

(defn member-of [t x]
  ((checker t) x))

(do :primitives

    (defn primitive-type [form pred]
      (type {:primitive true
             :form form}
            {:value-check
             (fn [_ v] (pred v))}))

    (def boolean (primitive-type :boolean boolean?))
    (def integer (primitive-type :integer integer?))
    (def float (primitive-type :float float?))
    (def string (primitive-type :string string?))
    (def keyword (primitive-type :keyword keyword?))
    (def symbol (primitive-type :symbol symbol?)))

(do :collections

    (def vector (primitive-type :vector vector?))
    (def list (primitive-type :list seq?))
    (def hash-map (primitive-type :hash-map map?))
    (def hash-set (primitive-type :hash-set set?))
    (def entry (primitive-type :entry map-entry?)))

(do :extremes

    (def void
      (type {:form :void
             :void true}
            {:value-check
             (fn [_ _] false)}))

    (def any
      (type {:form :any
             :any true}
            {:value-check
             (fn [_ _] true)})))

(do :combinators

    (defn type= [x y]
      ())

    (defn contains [x y]
      (let [x (->type x) y (->type y)]
        (cond
          (= x y) true
          (:any x) true
          (:any y) false
          (:void x) false
          (:void y) true
          (:union y) (every? (fn [m] (contains x m)) (:members y))
          (:union x) (some (fn [m] (contains m y)) (:members x))
          (:composition x) (every? (fn [m] (contains m y)) (:members x))
          (:composition y) (some (fn [m] (contains x m)) (:members y)) ;; wrong negatives here
          (:singleton y) (member-of x (:value y))
          (proto-get x :contains) (call-method x :contains y)
          (proto-get y :contained) (call-method y :contained x)
          (:primitive x) false
          (:singleton x) false
          :else (u/throw [::contains "no case:" x y]))))

    (defn unite [x y]
      (let [x (->type x) y (->type y)]
        (cond
          (contains x y) x
          (contains y x) y
          (:union y) (reduce unite x (:members y))
          (:union x) (update x :members conj y)
          :else (type {:union true
                       :members [x y]}
                      {:value-check
                       (fn union-check [this x]
                         (c/some (fn [m] (member-of m x))
                                 (:members this)))}))))

    (defn union [xs]
      (case (count xs)
        0 void
        1 (first xs)
        (reduce unite xs)))

    (defn compose [x y]
      (let [x (->type x) y (->type y)]
        (cond
          (contains x y) y
          (contains y x) x
          (:composition y) (reduce compose x (:members y))
          (:composition x) (update x :members (fn [ms] (-> (vec (remove (fn [m] (contains m y)) ms))
                                                          (conj y))))
          :else (type {:composition true
                       :members [x y]}
                      {:value-check
                       (fn [this x]
                         (every? (fn [m] (member-of m x))
                                 (:members this)))}))))

    (defn composition [xs]
      (case (count xs)
        0 any
        1 (first xs)
        (reduce compose xs)))

    (defn negation [t]
      (type {:negation true
             :type (->type t)}
            {:value-check
             (fn [this x] (not (member-of (:type this) x)))
             :contains
             (fn [this that]
               (if (:negation that)
                 (contains (:type that) (:type this))
                 (not (contains that (:type this)))))})))

(do :unions

    (def indexed (union [vector list]))
    (def hashed (union [hash-map hash-set]))
    (def number (union [integer float]))
    (def collection (union [vector list hash-map hash-set]))
    (def atomic (union [boolean integer float string keyword symbol])))

(do :compositions

    (defn contains-impl
      [tag key-or-keys]
      (let [inner-check
            (if (vector? key-or-keys)
              (fn [this that]
                (every? (fn [k] (contains (k this) (k that)))
                        key-or-keys))
              (fn [this that]
                (every? (fn [[a b]] (contains a b))
                        (c/map c/vector
                               (key-or-keys this)
                               (key-or-keys that)))))]
        (fn [this that]
          (and (tag that)
               (inner-check this that)))))

    (defn many [t]
      (type {:many true
             :element-type t}

            {:contains
             (contains-impl :many [:element-type])
             :value-check
             (fn many-check [this v]
               (and (coll? v)
                    (every? (checker (:element-type this)) v)))}))

    (defn entry-of [k v]
      (compose entry
               (type {:entry true
                      :key k :val v}
                     {:value-check
                      (fn [this x]
                        (and (member-of (:key this) (key x))
                             (member-of (:val this) (val x))))
                      :contains
                      (contains-impl :entry [:key :val])})))

    (defn vector-of [t]
      (compose vector (many t)))
    (defn list-of [t]
      (compose list (many t)))
    (defn map-of [k v]
      (compose hash-map (many (entry-of k v))))
    (defn set-of [t]
      (compose hash-set (many t)))

    (defn length [n]
      (compose collection
               (type {:length true
                      :value n}
                     {:value-check
                      (fn [this x]
                        (member-of (:value this) (count x)))
                      :contains
                      (contains-impl :length [:value])})))

    (defn tuple [xs]
      (composition [vector
                    (length (count xs))
                    (type {:zip true
                           :members xs}
                          {:value-check
                           (fn [this x]
                             (every? (fn [[a b]] (member-of a b))
                                     (map c/vector (:members this) x)))
                           :contains
                           (contains-impl :zip :members)})]))
    )

(do :extras

    (defn integer-range [min max]
      (compose integer
               (type {:range true
                      :min min
                      :max max}
                     {:value-check
                      (fn [this x]
                        (and (>= x (:min this))
                             (<= x (:max this))))
                      :contains
                      (fn [this that]
                        (and (:range that)
                             (<= (:min this) (:min that))
                             (>= (:max this) (:max that))))})))

    (defn transition [from to]
      (type {:transition true
             :from from
             :to to}
            {:value-check
             (fn [_ _] false)
             :contains
             (contains-impl :transition [:from :to])}))

    (defn typed-transition [f from to]
      (compose (transition from to) (singleton f)))

    (contains (transition number number)
              (typed-transition inc integer integer)))


(do :scratch
    (entry-of keyword vector)

    (let [t1 (union [integer list boolean])
          t2 (union [integer list keyword])]
      [(contains t1 t2)
       (contains t2 t1)
       (compose t1 t2)])

    (let [t1 (composition [integer list boolean])
          t2 (composition [integer list keyword])]
      [(contains t1 t2)
       (contains t2 t1)]))

(do :checks

    (assert
     (and (member-of (set-of number)
                     #{1 2 3})

          (member-of (tuple [keyword number])
                     [:ok 1])))

    (assert
     (and (contains vector vector)
          (contains indexed vector)
          (contains collection hashed)
          (contains (vector-of number) (vector-of integer))
          (contains (map-of atomic number) (map-of string integer))
          (contains (many integer) (vector-of integer))
          (contains (length 3) (length 3))
          (contains indexed  (compose vector (length 3)))
          (contains (tuple [number indexed])
                    (tuple [integer vector]))))

    (do :negation

        (assert
         (and (contains integer
                        (compose integer (negation 1)))

              (not (contains (compose integer (negation 1))
                             integer))

              (not (contains (negation 1)
                             1))

              (contains (negation 1)
                        2)

              (not (contains (compose integer (negation 1))
                             1))

              (contains (compose integer (negation 1))
                        2)

              (contains (negation integer)
                        (negation number))

              (not (contains (negation number)
                             (negation integer))))))

    (assert
     (let [t (length (union [2 3 4]))
           f (partial contains t)]
       (and (f [2 3])
            (f [2 4 5])
            (not (f [3]))
            (not (contains (compose list t) [2 3])))))

    (assert
     (let [t (integer-range 3 7)
           f (partial contains t)]
       (and (f 4)
            (f 7)
            (f (integer-range 3 6))
            (f (union [4 6]))
            (not (f 8))
            (not (f (integer-range 4 9)))))))

(do :difference

    (defn difference
      [x y]
      (let [x (->type x) y (->type y)]
        (cond
          (:void x) x
          (:void y) x
          (:any y) void
          (:any x) (negation y)
          (:singleton x) void
          (:union y) (reduce difference x (:members y))
          (:union x) (union (map (fn [m] (difference m y)) (:members x)))))))
