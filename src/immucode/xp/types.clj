(ns immucode.xp.types
  (:require [immucode.control :refer [?]]))

(defn with-proto [x & {:as p}]
  (with-meta x {::proto p}))

(defn get-proto [x]
  (some-> x meta ::proto))

(defn get-method [x k]
  (some-> (get-proto x) k))

(defn singleton? [x]
  (not (get-proto x)))

(def EMPTY
  (with-proto `EMPTY
    :intersect (constantly EMPTY)
    :fits (constantly true)))

(defn empty-type? [x]
  (= EMPTY x))

(def ANY
  (with-proto `ANY
    :intersect identity
    :contains (constantly true)))

(defn any-type? [x]
  (= ANY x))

(defn contains [t1 t2]
  (or (= t1 t2)
      (? [f (get-method t1 :contains)]
         (f t2))
      (? [f (get-method t2 :fits)]
         (f t1))))

(defn fits [t1 t2]
  (contains t2 t1))

(defn intersect [t1 t2]
  (?
   (contains t1 t2) t2
   (contains t2 t1) t1
   [f (get-method t1 :intersect)] (f t2)
   [f (get-method t2 :intersect)] (f t1)
   EMPTY))

(defn union
  [xs]
  (let [members
        (reduce (fn [ms x]
                  (?
                   [xs (::union x)] (into ms xs)
                   (= x EMPTY) ms
                   (conj ms x)))
                #{} xs)]

    (case (count members)
      0 EMPTY
      1 (first members)
      (with-proto {::union members}
        :intersect
        (fn [t]
          (union (map (partial intersect t) members)))
        :contains
        (fn [t]
          (boolean (some (partial fits t) members)))
        :fits
        (fn [t]
          (every? (partial contains t) members))))))

(do :checks

    (assert (= (intersect 1 1)
               1))

    (assert (and (contains ANY 1)
                 (contains 1 EMPTY)
                 (= EMPTY (intersect EMPTY 1))
                 (= 1 (intersect ANY 1))))

    (assert (= (intersect (union [1 2 3]) (union [2 5 7]))
               2))

    (assert (= (intersect (union [1 2 3]) (union [2 3 7]))
               (union [2 3])))

    (assert (contains (union [1 2 3]) 1))
    (assert (contains (union [1 2 3]) (union [1 2 3])))
    (assert (contains (union [1 2 3]) (union [2 3]))))

(defn from-pred [name f]
  (with-proto {::pred name}
    :contains f))

(do :checks

    (assert (= (intersect (from-pred :vec vector?)
                          [1 2 3])
               [1 2 3]))

    (assert (let [t (union [(from-pred :vec vector?)
                            (from-pred :seq seq?)])]
              (and (= (intersect t [1 2 3])
                      [1 2 3])
                   (= (intersect t (range 3))
                      (range 3))
                   (= EMPTY (intersect t {:a 1}))

                   (= (intersect t (union [[1 2] 4 (range 3)]))
                      (union [[1 2] (range 3)]))))))

(defn compose [xs]

  (if (some empty-type? xs)

    EMPTY

    (let [members (vec (keep (complement any-type?) xs))]

      (with-proto {::comp members}

        :intersect
        (fn [t]
          (loop [ret t todo members]
            (if-let [[m & todo] (seq todo)]
              (let [ret (intersect t m)]
                (if (empty-type? ret)
                  ret
                  (recur ret todo)))
              ret)))

        :contains
        (fn [t]
          (loop [xs members]
            (if-let [[x & xs] (seq xs)]
              (and (contains x t)
                   (recur xs))
              true)))

        :fits
        (fn [t]
          (loop [xs members]
            (if-let [[x & xs] (seq xs)]
              (and (fits x t)
                   (recur xs))
              true)))))))

(defn tuple [xs]
  (with-proto {::tuple xs}
    ))
