(ns immucode.path
  (:require [immucode.utils :as u]))

(defn path
  ([x]
   (cond
     (ident? x) (u/named->path x)
     (vector? x) (vec (mapcat path x))))
  ([x & xs]
   (path (into [x] xs))))

(defn path? [x]
  (and (vector? x)
       (every? symbol? x)))
