(ns immucode.tree
  (:refer-clojure :exclude [find])
  (:require [immucode.path :as path]
            [immucode.utils :as u]))

(defn cd
  [tree path]
  (if (empty? path)
    tree
    (let [s (first path)]
      (when-let [subtree (get-in tree [::node s])]
        (cd (assoc subtree ::parent tree ::name s)
            (next path))))))

(defn parent
  [{:as tree ::keys [parent name]}]
  (when parent
    (assoc-in parent [::node name]
              (dissoc tree ::parent ::name))))

(defn nth-ancestor
  [tree n]
  (nth (iterate parent tree) n))

(defn root [tree]
  (if-let [parent (parent tree)]
    (root parent)
    tree))

(defn root? [tree]
  (not (parent tree)))

(defn at [tree path]
  (cd (root tree) path))

(defn find
  [tree path]
  (when tree
    (or (cd tree path)
        (find (parent tree) path))))

(defn position
  [{:as _tree ::keys [parent name]}]
  (if parent
    (conj (position parent) name)
    []))

(defn upd
  [tree path f]
  (-> (f (cd tree path))
      (nth-ancestor (count path))))

(defn subnode-path [path]
  (interleave (repeat ::node) path))

(defn ensure-path
  [tree path]
  (if (seq path)
    (update-in tree
               (subnode-path path)
               (fn [x] (or x {})))
    tree))

(defn put
  ([tree path k v]
   (if (seq path)
     (update-in tree
                (subnode-path path)
                assoc k v)
     (assoc tree k v)))
  ([tree path m]
   (reduce (fn [e [k v]] (put e path k v)) tree m)))

(defn children [tree]
  (if-let [node (::node tree)]
    (mapv (fn [k] (cd tree [k]))
          (keys node))))

(do :show

    (defn- remove-parents
      [tree]
      (-> (dissoc tree ::parent ::name)
          (update ::node u/$vals remove-parents)))

    (defn show
      [tree]
      (-> (remove-parents tree)
          (assoc ::at (position tree))))

    (defn ppr [tree] (u/ppr (show tree))))


(comment :tries

         ())
