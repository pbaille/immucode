(ns immucode.path
  (:require [immucode.utils :as u]))

(defn path
  ([x]
   (cond
     (ident? x) (u/named->path x)
     (number? x) [x]
     (vector? x) (vec (mapcat path x))))
  ([x & xs]
   (path (into [x] xs))))

(defn path-segment? [x]
  (or (ident? x)
      (number? x)))

(defn path? [x]
  (and (vector? x)
       (every? path-segment? x)))

(defn parent-of [p c]
  (= p (vec (take (count p) c))))

(defn remove-prefix [p pref]
  (if (parent-of pref p)
    (vec (drop (count pref) p))))
