(ns immucode.xp.types2
  (:refer-clojure :exclude [type symbol keyword vector list hash-map hash-set])
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
  ((proto-get x k) x y))

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
          (:composition y) (some (fn [m] (contains x m)) (:members y))
          (:singleton y) (member-of x (:value y))
          (proto-get x :contains) (call-method x :contains y)
          (proto-get y :contained) (call-method y :contained x))))

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
          (:composition x) (update x :members conj y)
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
        (reduce compose xs))))

(do :unions

    (def indexed (union [vector list]))
    (def hashed (union [hash-map hash-set]))
    (def number (union [integer float]))
    (def collection (union [vector list hash-map hash-set]))
    (def atomic (union [boolean integer float string keyword symbol])))

(do :compositions

    (defn many [t]
      (type {:many true
             :element-type t}

            {:contains
             (fn [this x]
               (and (:many x)
                    (contains (:element-type this) (:element-type x))))

             :value-check
             (fn many-check [this v]
               (and (coll? v)
                    (every? (checker (:element-type this)) v)))}))

    (defn vector-of [t]
      (composition [vector (many t)]))
    (defn list-of [t]
      (composition [list (many t)]))
    (defn map-of [k v]
      (composition [hash-map (many (entry k v))]))
    (defn set-of [t]
      (composition [hash-set (many t)]))

    (defn length [n]
      (composition [collection
                    (type {:length true
                           :value n}
                          {:value-check
                           (fn [this x]
                             (= (:value this) (count x)))})]))

    (defn tuple [xs]
      (composition [vector
                    (length (count xs))
                    (type {:zip true
                           :members xs}
                          {:value-check
                           (fn [this x]
                             (every? (fn [[a b]] (contains a b))
                                     (map c/vector (:members this) x)))})]))
    )

(do :checks

    (assert (member-of (set-of number)
                       #{1 2 3}))

    (assert
     (and (contains vector vector)
          (contains indexed vector)
          (contains collection hashed)
          (contains (vector-of number) (vector-of integer))
          (contains (map-of atomic number) (map-of string integer))
          (contains (many integer) (vector-of integer))))

    (= (length 3) (length 3)))
