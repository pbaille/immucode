(ns immucode.composite-literals
  (:require [immucode.utils :as u :refer [cp]]))

(defn $ [x f]
  (cp x
      seq? (map f x)
      vector? (mapv f x)
      map? (into {} (map f x))
      set? (into #{} (map f x))))

(def dot '.)
(def dotdot '..)
(defn dot? [x] (= dot x))
(defn dotdot? [x] (= dotdot x))

(defn verb [x]
  (and (seq? x) (first x)))

(defn verb= [x v]
  (and (seq? x) (= v (first x))))

(defn quote? [x]
  ('#{quote qt} (verb x)))

(defn- dot-split
  "split a collection at first encountered dot,
  keeping it as the head of the second part"
  [c]
  (split-with (complement '#{. ..}) c))

(def dotted?
  (fn [x]
    (cp x
        map? (contains? x dot)
        sequential? (some dot? x)
        nil)))

(defn composed?
  "x contains some composition operators
   (. and/or ..)"
  [x]
  (cp x
      quote? nil
      map? (or (contains? x dot) (contains? x dotdot))
      sequential? (or (some dot? x) (some dotdot? x))
      nil))

(defn not-composed? [x]
  (not (composed? x)))

(defn single-dotted?
  "x has only one dot (useful in bind)"
  [x]
  (and (dotted? x)
       (cp x
           map? (not (contains? x dotdot))
           sequential?
           (and (not (some dotdot? x))
                (= 1 (count (filter dot? x)))))))

(defn seq-parts [s]
  (loop [xs s ret []]
    (if-let [[fs ss & rs] (seq xs)]
      (cp fs
          dot? (if (vector? ss)
                 ;; a dot is followed by a literal vector (for some reasons...)
                 (recur (concat ss rs) ret)
                 (recur rs (conj ret ss)))
          dotdot? (vec (concat (conj ret ss) rs))
          (recur (and (next xs) (cons ss rs))
                 (if (vector? (last ret))
                   (conj (vec (butlast ret)) (conj (last ret) fs))
                   (conj ret [fs]))))
      ret)))

(declare expand)

(defn expand-map [x]
  (let [dotpart (get x dot)]
    (list* `merge
           (expand (dissoc x dot))
           (if (vector? dotpart)
             (map expand dotpart)
             [(expand dotpart)]))))

(defn expand-seq [x]
  (if (dot? (first x))
    (throw "not supported (dot in verb position)")
    (let [[p1 & ps] (seq-parts x)]
      (if (seq ps)
        `(apply ~@p1
                ~(if (next ps)
                   `(concat ~@(map expand ps))
                   (expand (first ps))))
        (expand (seq p1))))))

(defn expand-vec [x]
  `(vec (concat ~@(map expand (seq-parts x)))))

(defn expand [x]
  (cp x

      composed?
      (cp x
          vector? (expand-vec x)
          seq? (expand-seq x)
          map? (expand-map x))

      coll?
      ($ x expand)

      x))

(comment (seq-parts '(a . (b c d)))
         (expand '(+ 1 . [2 3]))
         (expand '(+ 1 . xs 4))
         )
