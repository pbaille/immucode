(ns immucode.xp.types
  (:require [immucode.control :refer [f? ? AND OR]]
            [immucode.utils :as u]))

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

(defn compose [xs]

  (if (some empty-type? xs)

    EMPTY

    (let [members (vec (filter (complement any-type?) xs))]

      (with-proto {::comp members}

        :intersect
        (fn [t]
          (loop [ret t todo members]
            (if-let [[m & todo] (seq todo)]
              (let [ret' (intersect ret m)]
                (if (empty-type? ret')
                  EMPTY
                  (recur ret' todo)))
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
          (fits (first members) t))))))

(defn from-pred [name f]
  (with-proto {::pred name}
    :contains
    (fn [t]
      (f t))))

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
                      (union [[1 2] (range 3)])))))

    (let [vec (from-pred :vec vector?)
          len3 (from-pred :len3 #(= 3 (count %)))
          t (compose [vec len3])]
      (and (intersect t [2 3 4])
           (every? (comp empty-type? (partial intersect t))
                   [(range 3) [2 3] 4])
           (contains vec t))))

(defn tuple [xs]
  (with-proto {::tuple xs}
    ))










(defn zip-check [preds args]
  (if-let [[p & ps] (seq preds)]
    (and (p (first args))
         (zip-check ps (rest args)))
    true))

(defn dispatcher
  [cases]
  (fn [args]
    (loop [xs cases]
      (if-let [[x & xs] (seq xs)]
        (if (zip-check (get x 0) args)
          (get x 1)
          (recur xs))
        (u/throw [::dispatch args])))))

(def contains-cases
  (list
   [[::any any?] (fn [_ _ _] true)]
   [[::void any?] (fn [_ _ _] false)]
   [[singleton? any?] (fn [_ x y] (= x y))]
   [[::union ::union] (fn [contains u {xs ::union}] (every? (partial contains u) xs))]
   [[::union any?] (fn [contains {xs ::union} t] (some (fn [x] (contains x t)) xs))]
   [[any? singleton?] (fn [_ x y] (= x y))]))

(defn contains-fn [cases]
  (let [dispatch (dispatcher cases)]
    (fn self [x y]
      ((dispatch [x y]) self x y))))

((contains-fn contains-cases)
 (union [1 2])
 1)
((contains-fn contains-cases)
 (union [1 2 3])
 (union [1 2]))
