(ns immucode.xp.types3
  (:refer-clojure :exclude [compare type boolean float symbol keyword vector-of vector list hash-map hash-set])
  (:require [clojure.core :as c]
            [immucode.utils :as u]))

(do :type&proto

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
        (f x y))))

(do :value-check

    (defn value-checker [t]
      (let [t (->type t)]
        (-> t meta ::proto :value-check (partial t))))

    (defn value-check [t x]
      (let [t (->type t)
            f (-> t meta ::proto :value-check)]
        (f t x))))

(do :any_void_single

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
               (= (:value this) x))})))

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

(do :compare

    (defn comparison_flip [x]
      (case x
        :smaller :bigger
        :bigger :smaller
        :distinct :distinct
        :overlap :overlap
        :equal :equal
        nil))

    (defn comparison_unite [x y]
      (if (= x y)
        x
        (let [cs #{x y}]
          (or (cs :bigger)
              (if (cs :equal)
                (if (or (cs :distinct) (cs :overlap))
                  :bigger
                  :equal))
              (cs :overlap)
              (cs :distinct)))))

    (defn compare [a b]
      (or (and (= a b) :equal)
          (call-method a :compare b)
          (comparison_flip (call-method b :compare a))
          nil #_(u/throw [::compare a b]))))

(declare union intersection)

(do :union

    (defn compare-unions
      [this that]
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
            :else :overlap))))

    (defn unchecked-union [a b]
      (type {:union true
             :left a
             :right b}
            {:compare
             (fn [this that]
               (if (:union that)
                 (compare-unions this that)
                 (let [left-comparison (compare (:left this) that)]
                   (if (= :bigger left-comparison)
                     :bigger
                     (comparison_unite
                      left-comparison
                      (compare (:right this) that))))))

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
        (reduce unite (map ->type xs)))))

(do :intersection

    (defn comparison_intersect [x y]
      #_(println "comparison_intersect " x y)
      (if (= x y)
        x
        (let [cs #{x y}]
          (or (cs :distinct)
              (cs :smaller)
              (if (cs :equal)
                (if (cs :bigger)
                  :equal
                  :smaller))
              (cs :overlap)))))

    (defn compare-intersection [this that]
      (let [left-comparison (compare (:left this) that)]
        (if (or (= :distinct left-comparison)
                (= :smaller left-comparison))
          left-comparison
          (comparison_intersect
           left-comparison
           (compare (:right this) that)))))

    (defn compare-intersections
      [{:as this l1 :left r1 :right}
       {:as that l2 :left r2 :right}]

      (or (and (= l1 r2)
               (= l2 r1)
               :equal)

          (let [c1 (compare this l2)
                c2 (compare this r2)
                cs (c/set [c1 c2])]

            (cond

              (cs :distinct) :distinct

              (or (cs :equal)
                  (cs :bigger)) :bigger

              (= :smaller c1 c2)
              (if (and (= :smaller (compare that l1))
                       (= :smaller (compare that r1)))
                :equal
                :smaller)

              :else
              (let [ll (compare l1 l2)
                    lr (compare l1 r2)
                    rl (compare r1 l2)
                    rr (compare r1 r2)
                    xs (c/set [ll lr rl rr])]
                (cond (xs :distinct) :distinct
                      (or (= :equal ll rr)
                          (= :equal lr rl)) :equal))))))

    (defn unchecked-intersection [a b]
      (type {:intersection true
             :left a
             :right b}
            {:compare
             (fn [this that]
               (or (and (:intersection that)
                        (compare-intersections this that))
                   (compare-intersection this that)))

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

(do :primitives-groups

    (def indexed (union [vector list]))
    (def hashed (union [hash-map hash-set]))
    (def number (union [integer float]))
    (def collection (union [vector list hash-map hash-set]))
    (def atomic (union [boolean integer float string keyword symbol])))

(do :extras

    (defn derived-type [parent this]
      (let [proto (proto this)
            compare-method (get proto :compare)
            value-check-method (get proto :value-check)]
        (type this
              (assoc (proto this)
                     :compare
                     (fn [this that]
                       (let [comparison (compare parent that)]
                         (case comparison
                           :distinct :distinct
                           (:smaller :equal) :smaller
                           (compare-method this that))))
                     :value-check
                     (fn [this x]
                       (and (value-check parent x)
                            (value-check-method this x)))))))

    (defn many [t]
      (derived-type
       collection
       (type {:many true
              :element-type (->type t)}

             {:compare
              (fn [this that]
                (cond (:many that)
                      (compare (:element-type this) (:element-type that))))
              :value-check
              (fn many-check [{t :element-type} xs]
                (every? (partial (proto-get t :value-check) t)
                        xs))})))

    (defn entry-of [k v]
      (derived-type
       entry
       (type {:entry true
              :key k :val v}
             {:compare
              (fn [this that]
                (cond (:entry that)
                      (comparison_intersect
                       (compare (:key this) (:key that))
                       (compare (:val this) (:val that)))))
              :value-check
              (fn [this x]
                (and (call-method (:key this) :value-check (key x))
                     (call-method (:val this) :value-check (val x))))})))

    (defn length [n]
      (derived-type
       collection
       (type {:length true
              :value (->type n)}
             {:value-check
              (fn [this x]
                (value-check (:value this) (count x)))
              :compare
              (fn [this that]
                (cond (:length that) (compare (:value this) (:value that))
                      (:primitive that) :overlap))})))

    (defn tuple [xs]
      (derived-type
       vector
       (derived-type
        (length (single (count xs)))
        (type {:zip true
               :members xs}
              {:value-check
               (fn [this x]
                 (every? (fn [[a b]] (value-check a b))
                         (map c/vector (:members this) x)))
               :compare
               (fn [this that]
                 (cond (:zip that)
                       (let [comparisons
                             (-> (c/map compare
                                        (:members this)
                                        (:members that))
                                 (c/set) (disj :equal))]
                         (case (count comparisons)
                           0 :equal
                           1 (first comparisons)
                           :overlap))))}))))

    (defn negation [t]
      (type {:negation true
             :type (->type t)}
            {:value-check
             (fn [this x]
               (not (value-check (:type this) x)))
             :compare
             (fn [this that]
               (cond (:negation that)
                     (compare (:type that) (:type this))
                     :else (case (compare (:type this) that)
                             :smaller :overlap
                             (:bigger :equal) :distinct
                             :overlap :overlap
                             :distinct :smaller)))})))

(do :uniform-collections

    (defn vector-of [t]
      (intersect vector (many t)))
    (defn list-of [t]
      (intersect list (many t)))
    (defn map-of [k v]
      (intersect hash-map (many (entry-of k v))))
    (defn set-of [t]
      (intersect hash-set (many t))))

#_(u/throw :stop)
(do :scratch

    (let [not1 (negation 1)
          not-int (negation integer)]
      [(value-check not1 2)
       (false? (value-check not1 1))
       (compare not1 not1)
       (compare not1 not-int)
       (compare not1 integer)
       (compare (intersect integer not1) integer)
       (value-check (intersect integer not1) 1)]))








































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
                    (union [vector string])]))))

(assert
 (= :bigger
    (compare collection
             (single [1 2 3]))))

(assert
 (= :bigger
    (compare (many integer)
             (single [1 2 3]))
    (compare collection
             (many integer))
    (compare (many number)
             (many integer))))

(assert
 (and (value-check (length 3)
                   [1 2 3])
      (false? (value-check (length 2)
                           [1 2 3]))
      (value-check (length (union [2 3]))
                   [2 3])
      (value-check (length (union [2 3]))
                   [1 2 3])
      (false?
       (value-check (length (union [2 3]))
                    [1]))

      (value-check (tuple [integer string])
                   [1 "iop"])))

(assert (and (= (length 3) (length 3))
             (= :overlap
                (compare (length 3) vector))
             (= :smaller
                (compare (intersection [vector (length 3)]) (length 3)))
             (= :overlap
                (compare (intersection [vector (length (union [2 3 4]))]) (length 3)))))

(assert
 (and (= :equal
         (compare (unchecked-intersection vector (length 3))
                  (unchecked-intersection vector (length 3)))
         (compare (unchecked-intersection (length 3) vector)
                  (unchecked-intersection vector (length 3))))

      (= :bigger
         (compare (tuple [number string])
                  (tuple [integer string]))
         (compare (length 3)
                  (unchecked-intersection vector (length 3)))
         (compare vector
                  (unchecked-intersection vector (length 3))))
      (= :smaller
         (compare (tuple [integer string])
                  (tuple [number string])))))
