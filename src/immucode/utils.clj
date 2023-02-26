(ns immucode.utils
  (:refer-clojure :exclude [throw])
  (:require [clojure.string :as str]
            [clojure.pprint :as pprint]))

(defn map-entry [k v]
  (clojure.lang.MapEntry. k v))

(defmacro cp [& body]
  `(condp #(%1 %2) ~@body))

(defn quote? [x]
  (and (seq? x) (= 'quote (first x))))

(defn quote-wrap [x]
  (list 'quote x))

(defn named? [x]
  (or (string? x) (keyword? x) (symbol? x)))

(defn named->path [x]
  (when (and (named? x) (not (namespace x)))
    (mapv symbol
          (str/split (name x) #"\."))))

(defn concatv [& xs]
  (reduce into [] xs))

(defn member? [xs e]
  (contains? (set xs) e))

(defn indexof [xs e]
  (and (member? xs e)
       (loop [i 0 [x & xs] xs]
         (if (= x e)
           i (recur (inc i) xs)))))

(defn $vals
  [m f]
  (into {} (map (fn [[k v]] [k (f v)]) m)))

(defn $ [x f]
  (cond (seq? x) (map f x)
        (vector? x) (mapv f x)
        (map? x) (into {} (map f x))
        (set? x) (into #{} (map f x))))

(defn $i [x f]
  (cond (seq? x) (map f (range (count x)) x)
        (vector? x) (vec (map f (range (count x)) x))
        (map? x) (into {} (map (fn [[k v]] [k (f k v)]) x))
        (set? x) (into #{} (map f x x))))

(defn kv-seq [x]
  (cond (sequential? x) (map vector (range) x)
        (map? x) (map identity x)
        (set? x) (map vector x x)))

(defn ppr [& xs]
  (mapv pprint/pprint xs)
  (last xs))

(defn pretty-str [& xs]
  (with-out-str
    (apply ppr xs)))

(defn ppx [x]
  (ppr (macroexpand-1 x)))

(defn throw [& xs]
  (throw (Exception. (apply pretty-str xs))))

(defmacro is [& xs]
  `(or (= ~@xs)
       (throw (into [:not-equal] '~xs))))

(defn collection-type [x]
  (cond (seq? x) :list
        (map? x) :hash-map
        (vector? x) :vector
        (set? x) :hash-set))

(defn simple-type [x]
  (cond (fn? x) :function
        (coll? x) (collection-type x)
        (number? x) :number
        (string? x) :string
        (symbol? x) :symbol
        (keyword? x) :keyword
        (boolean? x) :boolean))

(defn prob [& xs]
  (mapv ppr xs)
  (last xs))

(defmacro type-case [x & xs]
  `(case (simple-type ~x) ~@xs))

(defmacro with-gensyms [xs & body]
  `(let [~xs (map gensym ~(mapv #(str (name %) "_") xs))]
     ~@body))

(defn pairs&return [xs]
  (if (odd? (count xs))
    [(partition 2 (butlast xs)) (last xs)]
    [(partition 2 xs) nil]))
