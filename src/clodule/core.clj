(ns clodule.core
  (:refer-clojure :exclude [= -])
  (:require [clojure.core :as core]
            [clojure.string :as str]
            [me.raynes.fs :as fs]
            [clojure.pprint :as pp]))

"This code comes from beop-xp/belt"

(do :utils

    (defn pretty-str [x]
      (with-out-str (pp/pprint x)))

    (defn split-by [f xs]
      (reduce (fn [ret x]
                (update ret (if (f x) 0 1) conj x))
              [[] []] xs))

    (defn quoted [x]
      (list 'quote x))

    (defn verb= [v expr]
      (and (seq? expr) (core/= v (first expr)))))

(do :parse

    (def sym->type
      '{- :module
        = :definition})

    (def module-expr? (partial verb= '-))

    (def definition-expr? (partial verb= '=))

    (declare expand-definition expand-module)

    (defn expand [at x]
      (cond (module-expr? x) (expand-module at (rest x))
            (definition-expr? x) (expand-definition at (rest x))))

    (defn expand-module-form [form]
      (when-let [[verb & args] (and (seq? form) form)]
        (list* '- verb
               (map (partial list '-) args))))

    (defn expand-definition [at [pattern return]]
      {:type    :definition
       :at      at
       :pattern pattern
       :return  return})

    (defn split-meta [xs]
      (loop [meta {}
             todo xs]
        (if-let [[x & xs] (seq todo)]
          (if (keyword? x)
            (recur (assoc meta x (first xs)) (rest xs))
            [meta todo])
          [meta todo])))

    (defn expand-module [at [head & content]]
      (if (seq? head)
        (-> (expand-module
             at (into [(first head)]
                      (concat (map (partial list '-) (rest head))
                              content)))
            (assoc :form head))
        (let [[meta children] (split-meta content)]
          (merge meta
                 {:type     :module
                  :at       at
                  :name     head
                  :content (mapv (partial expand (conj at head)) children)}))))

    (defn module? [x]
      (core/= :module (:type x)))

    (defn definition? [x]
      (core/= :definition (:type x)))

    (defn submodules [module]
      (filter module? (:content module)))

    (defn definitions [module]
      (filter definition? (:content module))))

(do :emit

    (defn path [xs]
      (->> (map name xs)
           (mapcat #(str/split % #"\."))
           (str/join "/")))

    (defn source-path [xs]
      (str (path xs) ".clj"))

    (defn form->definitions [[verb & args]]
      (into [(list 'defn verb (vec args) ())]
            (map (fn [a]
                   (list 'defprotocol
                         :extend-via-metadata true
                         (symbol (str "I" (name a)))
                         (list (symbol (str "-" (name a))) '[_])))
                 args)))

    (declare compile!)

    (defn module->ns-sym [{:as m :keys [:name :at]}]
      (when (module? m)
        (symbol (str/join "." (conj at name)))))

    (defn module-require-form [m]
      (if-let [aliases (seq (merge (:alias m) (zipmap (:use m) (:use m))))]
        (list* :require (map (fn [[k v]] [(symbol (str/join "." (conj (:at m) v))) :as k])
                             aliases))))

    (defn module-ns-form [m]
      (list* 'ns (module->ns-sym m)
             (if-let [require (module-require-form m)]
               [require])))

    (defn compile-module! [from {:as m :keys [:name :at :content]}]
      (let [dir (into from at)
            filepath (source-path (conj dir name))]
        (fs/touch filepath)
        (spit filepath (pretty-str (module-ns-form m)))
        (when-let [submodules (seq (submodules m))]
          (fs/mkdirs (path (conj dir name))))
        (doseq [child content]
          (compile! from child))))

    (defn compile-definition [{:keys [:at :pattern :return]}]
      (cond
        (list? pattern) (list 'defn (first pattern) (vec (rest pattern)) return)
        (symbol? pattern) (list 'def pattern return)))

    (defn append-definition! [from d]
      (let [filepath (source-path (into from (:at d)))]
        (spit filepath
              (str (slurp filepath)
                   "\n"
                   (pretty-str (compile-definition d))))))

    (defn compile!
      ([x] (compile! '[scratch generated] x))
      ([from x]
       (case (:type x)
         :definition (append-definition! from x)
         :module (compile-module! from x)))))

(defmacro code [& form]
   (compile! '[target src]
             (expand-module [] form)))

(code moi
      (- je
         (= suis :top))
      (- seul
         (- au
            (= monde :vraiment))))

(code ex1
      (- math
         (= add +)
         (= div /))
      (- stats
         :use [math]
         (= (mean xs)
            (math/div
             (reduce math/add xs)
             (count xs))))
      (- scratch
         :use [stats]
         (= x (stats/mean [1 2 3 4]))))
