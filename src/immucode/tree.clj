(ns immucode.tree
  (:refer-clojure :exclude [find])
  (:require [immucode.path :as path]))

(defn cd
  [tree path]
  (if (empty? path)
    tree
    (let [s (first path)]
      (when-let [subtree (get-in tree [:node s])]
        (cd (assoc subtree :parent tree :name s)
            (next path))))))

(defn parent
  [{:as tree :keys [parent name]}]
  (when parent
    (assoc-in parent [:node name]
              (dissoc tree :parent :name))))

(defn nth-ancestor
  [tree n]
  (nth (iterate parent tree) n))

(defn root [tree]
  (if-let [parent (parent tree)]
    (root parent)
    tree))

(defn find
  [tree path]
  (when tree
    (or (cd tree path)
        (find (parent tree) path))))

(defn position
  [{:as _tree :keys [parent name]}]
  (if parent
    (conj (position parent) name)
    []))

(defn upd
  [tree path f]
  (-> (f (cd tree path))
      (nth-ancestor (count path))))

(defn subnode-path [path]
  (interleave (repeat :node) path))

(defn ensure-path
  [tree path]
  (if (seq path)
    (update-in tree
               (subnode-path path)
               (fn [x] (or x {})))
    tree))

(defn put [tree path k v]
  (update-in tree
             (subnode-path path)
             assoc k v))

(comment :leaf-stuff

         (defn set-leaf
           ([tree v]
            (assoc tree :leaf v))
           ([tree path v]
            (upd tree path
                 #(set-leaf % v))))

         (defn put-leaf [tree path v]
           (-> (ensure-leaf tree path)
               (set-leaf path v)))

         (defn put-leaves [tree xs]
           (reduce (fn [t [sym val]]
                     (put-leaf t (path/path sym) val))
                   tree (partition 2 xs)))

         (defn upd-leaf
           ([tree f]
            (if (contains? tree :leaf)
              (update tree :leaf f)
              tree))
           ([tree path f]
            (upd tree path
                 #(upd-leaf % f))))

         (defn upd-node
           [tree f]
           (reduce #(-> (cd % [%2]) f parent)
                   tree (keys (:node tree))))

         (defn upd-leaves
           [tree f]
           (-> (upd-leaf tree f)
               (upd-node #(upd-leaves % f)))))

(defmacro at [tree path & ops]
  `(upd ~tree ~path
        (fn [t#] (-> t# ~@ops))))
