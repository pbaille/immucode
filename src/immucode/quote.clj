(ns immucode.quote
  (:require [immucode.composite-literals :as composite]
            [immucode.utils :as u :refer [cp]]))

(defn verb [x]
  (when (seq? x) (first x)))

(defn quote? [x]
  (contains? '#{qt quote} (verb x)))

(defn unquote? [x]
  ('#{unquote clojure.core/unquote unq} (verb x)))

(defn unquote-quote? [x]
  (or (and (unquote? x)
           (quote? (second x)))))

(defn up-quote? [x]
  ('#{up-qt upq} (verb x)))

(defn up-quote-unquote? [x]
  (= (verb x) 'upnq))

(defn quote-wrap [x]
  (list 'quote x))

(defn quote-fn [lvl form]

  (cp form

      ;; we do not touch dots
      ;; dot? dot
      ;; dotdot? dotdot

      ;; bubling up one quote level
      unquote-quote? (recur (dec lvl) (second (second form)))

      ;; unquote
      unquote? (if (zero? lvl)
                 (second form)
                 (list 'list
                       (quote-wrap 'unquote)
                       (quote-fn (dec lvl) (second form))))

      ;; nested quote
      quote? (list 'list
                   (quote-wrap (first form))
                   (quote-fn (inc lvl) (second form)))

      ;; shortcuts (not mandatory)
      ;qup
      up-quote? (recur (dec lvl) (second form))
      ;punq
      up-quote-unquote? (recur (dec lvl) (list 'unquote (second form)))

      ;; collections
      seq? (cons 'list (u/$ form #(quote-fn lvl %)))
      coll? (u/$ form #(quote-fn lvl %))

      ;; default
      (quote-wrap form)))

(defmacro qt [form]
  (quote-fn 0 form))

(comment

  (qt (a b c (unq (+ 1 2))))
  (let [x 1]
    (assert (= '(a (qt (b 1)))
               (qt (a (qt (b (upnq x)))))
               (qt (a (qt (b (upq (unq x))))))
               (qt (a (qt (b (unq (qt (unq x))))))))))

  (let [x 1
        l [1 2 3]]
    (composite/expand
      (qt (+ (unq x) . (unq l))))))
