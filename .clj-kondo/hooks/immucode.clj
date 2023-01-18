(ns hooks.immucode)

(defmacro program [& forms]
  `(-> ENV0
       ~@(map (fn [[verb & args]]
                (cons verb (map (fn [x] (list 'quote x)) args)))
              forms)))
