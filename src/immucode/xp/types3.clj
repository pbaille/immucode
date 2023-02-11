(ns immucode.xp.types3
  (:refer-clojure :exclude [compare type boolean float symbol keyword vector-of vector list hash-map hash-set])
  (:require [clojure.core :as c]
            [immucode.utils :as u]))

(defn type [data proto]
  (vary-meta data
             merge
             {::type true
              ::proto proto}))

(defn type? [x]
  (some-> x meta ::type))

(declare single)

(defn ->type [x]
  (if (type? x)
    x
    (single x)))

(defn proto [x]
  (-> (->type x) meta ::proto))

(defn proto-get [x k]
  (get (proto x) k))

(defn call-method [x k y]
  (if-let [f (proto-get x k)]
    (f x y)))

(comment
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

  (do :control-macros

      (defmacro or-some
        [& xs]
        (reduce (fn [ret e] `(if-some [x# ~e] x# ~ret))
                nil
                (reverse xs)))

      (defmacro and-some
        [& xs]
        (reduce (fn [ret e] `(if-not (nil? ~e) ~ret))
                nil
                (reverse xs)))

      (defmacro boolean-case
        [test if-true if-false & [if-nil]]
        `(case ~test
           true ~if-true
           false ~if-false
           nil ~if-nil))

      (defn not-some [x]
        (boolean-case x false true))

      (defmacro boolean-cases [& xs]
        (reduce (fn [ret [p t f]] `(boolean-case ~p ~t ~f ~ret))
                nil (reverse xs))))

  (do :xp1
      "methods of interest"
      "those checks return true, false or nil (cannot be determined)"
      [:contains
       :distinct]

      "those checks could be building block for other operations"
      {:select ""
       :retract ""
       :connect ""}

      (defn contains [x y]
        (or-some (call-method x :contains y)
                 (not-some (call-method y :contains x))))

      (defn distinct [x y]
        (or-some (call-method x :distinct y)
                 (call-method y :distinct x)))

      (defn select [x y]
        (boolean-case (contains x y)

                      [(distinct x y)
                       void
                       ]))


      (defn connect [x y]
        (or (call-method x :connect y)
            (call-method y :connect x)
            (boolean-cases
             [(contains x y) x y]
             [(intersects x y)
              (:unchecked-union x (retract x y))
              (:unchecked-union x y)])))

      (defn retract [x y]
        (or (call-method x :retract y)
            (boolean-cases
             [(contains x y)
              (:todo)
              void]
             [(intersects x y)
              (:todo)
              x])))
      ))

(do :xp2

    "compare"

    (def void (type {:void true}
                    {:compare
                     (fn [_ that]
                       (if (:void that)
                         :equal
                         :smaller))
                     :value-check
                     (fn [_ _] false)}))

    (def any (type {:any true}
                   {:compare
                    (fn [_ that]
                      (if (:any that)
                        :equal
                        :bigger))
                    :value-check
                    (fn [_ _] true)}))

    (do :primitives

        (defn primitive-type [form pred]
          (type {:primitive true
                 :form form}
                {:value-check
                 (fn [_ v] (pred v))
                 :compare
                 (fn [this that]
                   (cond (:primitive that) :distinct
                         (:single that) (if (pred (:value that)) :bigger :distinct)))}))

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

    (defn compare [a b]
      (or (and (= a b) :equal)
          (call-method a :compare b)
          (case (call-method b :compare a)
            :smaller :bigger
            :bigger :smaller
            :distinct :distinct
            :overlap :overlap
            :equal :equal
            (u/throw [::compare a b]))))

    (defn single [x]
      (type {:single true
             :value x}
            {:compare
             (fn [this that]
               (cond
                 (= that void) :bigger
                 (call-method that :value-check (:value this)) :smaller
                 :else :distinct))
             :value-check
             (fn [this x]
               (= (:value this) x))}))

    (declare union intersection)

    (defn unchecked-union [a b]
      (type {:union true
             :left a
             :right b}
            {:compare
             (fn [this that]
               (if (:union that)
                 (if (and (= (:left this) (:right that))
                          (= (:left that) (:right this)))
                   :equal
                   (let [c1 (compare this (:left that))
                         c2 (compare this (:right that))
                         cs (c/set [c1 c2])]
                     (cond
                       (cs :smaller) :smaller
                       (= :distinct c1 c2) :distinct
                       (cs :distinct) :overlap
                       (= :bigger c1 c2) (if (and (= :bigger (compare that (:left this)))
                                                  (= :bigger (compare that (:right this))))
                                           :equal
                                           :bigger)
                       :else :overlap)))
                 (let [lc (compare (:left this) that)
                       rc (compare (:right this) that)]
                   (if (= lc rc)
                     lc
                     (let [cs #{lc rc}]
                       (or (cs :bigger)
                           (if (cs :equal)
                             (if (or (cs :distinct) (cs :overlap))
                               :bigger
                               :equal))
                           (cs :overlap)
                           (cs :distinct)))))))

             :unite
             (fn [this that]
               (if (:union that)
                 (union [this (:left that) (:right that)])))

             :intersect
             (fn [this that]
               (if (:union that)
                 (union [(intersection [this (:left that)])
                         (intersection [this (:right that)])])))

             :value-check
             (fn [this x]
               (or (call-method (:left this) :value-check x)
                   (call-method (:right this) :value-check x)))}))

    (defn unite [a b]
      (case (compare a b)
        (:bigger :equal) a
        :smaller b
        (:distinct :overlap)
        (or (call-method a :unite b)
            (call-method b :unite a)
            (unchecked-union a b))))

    (defn union [xs]
      (case (count xs)
        0 void
        1 (->type (first xs))
        (reduce unite (map ->type xs))))

    (do :unions

        (def indexed (union [vector list]))
        (def hashed (union [hash-map hash-set]))
        (def number (union [integer float]))
        (def collection (union [vector list hash-map hash-set]))
        (def atomic (union [boolean integer float string keyword symbol])))

    (defn unchecked-intersection [a b]
      (type {:intersection true
             :left a
             :right b}
            {:compare
             (fn [this that]
               (or (and (:intersection that)
                        (or (and (= :equal (compare (:left this) (:left that)))
                                 (= :equal (compare (:right this) (:right that))))
                            (and (= :equal (compare (:left this) (:right that)))
                                 (= :equal (compare (:right this) (:left that)))))
                        :equal)

                   (let [lc (compare (:left this) that)
                         rc (compare (:right this) that)]
                     (if (= lc rc)
                       lc
                       (let [cs #{lc rc}]
                         (or (cs :distinct)
                             (cs :smaller)
                             (if (cs :equal)
                               (if (cs :bigger)
                                 :equal
                                 :smaller))
                             :overlap))))))

             :unite
             (fn [this that]
               ;; don't what to do here... necessary ?
               (cond
                 (:union that) nil
                 (:intersection that) nil))

             :intersect
             (fn [this that]
               (cond
                 (:union that)
                 (union [(intersection [this (:left that)])
                         (intersection [this (:right that)])])
                 (:intersection that)
                 (intersection [this (:left that) (:right that)])))

             :value-check
             (fn [this x]
               (and (call-method (:left this) :value-check x)
                    (call-method (:right this) :value-check x)))}))

    (defn intersect [a b]
      (case (compare a b)
        (:smaller :equal) a
        :bigger b
        :distinct void
        :overlap
        (or (call-method a :intersect b)
            (call-method b :intersect a)
            (unchecked-intersection a b))))

    (defn intersection [xs]
      (case (count xs)
        0 any
        1 (->type (first xs))
        (reduce intersect (map ->type xs)))))

(do :extras

    )

(do :scratch)

(do :checks
    (assert
     (and
      (= :equal
         (compare (single 2) (single 2)))

      (= :distinct
         (compare (single 1) (single 2)))

      (= :smaller
         (compare void (single 2)))

      (= :bigger
         (compare (single 2) void))

      (= :bigger
         (compare (union [1 2 3])
                  (single 1)))

      (= :smaller
         (compare (single 1)
                  (union [1 2 3])))

      (= :equal
         (compare (union [1 2])
                  (union [2 1])))

      (= :equal
         (compare (union [1 2 3])
                  (union [1 3 2])))

      (= :equal
         (compare
          (union [(union [1 2 3])
                  (union [2 3 4])])
          (union [1 2 3 4])))

      (= :equal
         (compare
          (union [1 2 3])
          (union [(union [1 2])
                  (union [2 3])])))

      (= :equal
         (compare (intersection [(union [indexed hash-map])
                                 (union [hashed vector])])
                  (union [hash-map vector])))))

    (assert
     (and

      (= (single 1)
         (union [1 1 1]))

      (= any
         (union [(union [1 2 3])
                 any])
         (union [any void]))

      (= void
         (intersection [1 2])
         (intersection [integer string])
         (intersection [collection string]))

      (= vector
         (intersection [(intersection [collection indexed])
                        (intersection [vector indexed])])
         (intersection [collection
                        (union [vector string])])))))
