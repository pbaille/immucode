(ns immucode.utils
  (:refer-clojure :exclude [throw])
  (:require [clojure.string :as str]
            [clojure.pprint :as pprint]))

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
  (cond (sequential? x) (map vector (range (count x)) x)
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

(defn throw [x]
  (throw (Exception. (pretty-str x))))

(defmacro is [& xs]
  `(or (= ~@xs)
       (throw (into [:not-equal] '~xs))))

(defn simple-type [x]
  (cond (fn? x) :function
        (coll? x)
        (cond (seq? x) :list
              (map? x) :hash-map
              (vector? x) :vector
              (set? x) :hash-set)
        (number? x) :number
        (string? x) :string
        (symbol? x) :symbol
        (keyword? x) :keyword))

(defn prob [& xs]
  (mapv ppr xs)
  (last xs))

(defmacro type-case [x & xs]
  `(case (simple-type x) ~@xs))