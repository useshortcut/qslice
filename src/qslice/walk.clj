(ns qslice.walk
  (:import
   (clojure.lang
    ArraySeq
    IMapEntry
    IObj
    IRecord
    MapEntry)
   (java.util
    Arrays)))

(set! *warn-on-reflection* true)

;; Public for tests only
(defn map-aseq
  "Map f over items in ArraySeq, returning a new ArraySeq with the result.

  ArraySeqs are seqs backed by a single object array. They are weird.
  Unlike most seqs but like vectors they are both indexed and counted.
  Unlike vectors but like seqs, accretion (e.g. conj) produces a cons.
  Like subvec, rest/next etc produce an ArraySeq which is a view of the original
  array, so they are intrinsically head-holding.
  They don't provide a chunked seq, so map and other seq functions produce
  an unchunked lazy-seq which can be quite space-inefficient.
  That is why this function exists.

  The most common source of these is sort or sort-by."
  ^ArraySeq [f ^ArraySeq xs]
  ;; index is where the ArraySeq's view of the backing array starts;
  ;; It is incremented by next or rest.
  ;; The array field is public because other places in clojure.core have similar
  ;; array-seq specializations.
  (let [i (.index xs)
        a (.array xs)
        b (Arrays/copyOfRange a i (alength a))
        blen (alength b)]
    (loop [ai (unchecked-int i) bi 0]
      (if (< bi blen)
        (do
          (aset b bi (f (aget a ai)))
          (recur (unchecked-inc-int ai) (unchecked-inc-int bi)))
        (ArraySeq/create b)))))

;; Copied and modified from potemkin,
;; v0.4.5 (https://github.com/ztellman/potemkin), MIT licensed, Copyright
;; Zachary Tellman

;; adapted from clojure.walk, but preserves metadata

(defn walk
  "Like `clojure.walk/walk`, but preserves metadata."
  [inner outer form]
  (let [x (cond
            (list? form) (outer (apply list (map inner form)))
            (instance? IMapEntry form)
            (outer (MapEntry/create (inner (key form)) (inner (val form))))
            (instance? ArraySeq form) (outer (map-aseq inner form))
            (seq? form) (outer (doall (map inner form)))
            (instance? IRecord form)
            (outer (reduce (fn [r x] (conj r (inner x))) form form))
            (coll? form) (outer (into (empty form) (map inner) form))
            :else (outer form))]
    (if (instance? IObj x)
      (with-meta x (merge (meta form) (meta x)))
      x)))

(defn postwalk
  "Like `clojure.walk/postwalk`, but preserves metadata."
  [f form]
  (walk (partial postwalk f) f form))

(defn prewalk
  "Like `clojure.walk/prewalk`, but preserves metadata."
  [f form]
  (walk (partial prewalk f) identity (f form)))

(defn postwalk-replace [smap form]
  (postwalk (fn [x] (if-some [[_ r] (find smap x)] r x)) form))
