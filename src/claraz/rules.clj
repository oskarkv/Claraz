(ns claraz.rules
  (:require
   [clara.rules.accumulators :as acc]
   [clara.rules.dsl :as dsl]
   [clara.rules.engine :as eng]
   [clojure.spec.alpha :as s]
   [clojure.string :as str]
   [clojure.walk :as walk]))

(defn- ?symbol?
  "Returns ture if symbol is a symbol that starts with ?."
  [sym]
  (and (symbol? sym) (str/starts-with? (str sym) "?")))

(s/def ::?symbol ?symbol?)

(s/def ::salience int?)

(s/def ::acc-vec
  (s/and vector? (s/cat :acc (s/? any?) :type symbol?)))

(s/def ::fact
  (s/cat :var (s/? ::?symbol)
         :type (s/or :simple symbol? :acc ::acc-vec)
         :destruct (s/? vector?)
         :exprs (s/* list?)))

(s/def ::fact-without-var
  (s/& ::fact #(nil? (:var %))))

(s/def ::test
  (s/cat :op #{:test} :expr list?))

(s/def ::not-exists
  (s/cat :op #{:not :exists}
         :arg (s/spec (s/alt :fact-without-var ::fact-without-var
                             :expr ::expr))))

(s/def ::and-or
  (s/cat :op #{:or :and}
         :args (s/+ (s/spec (s/alt :fact ::fact
                                   :expr ::expr)))))

(s/def ::expr
  (s/alt :and-or ::and-or
         :not-exists ::not-exists
         :test ::test))

(s/def ::cond
  (s/spec (s/alt :fact ::fact :expr ::expr)))

(s/def ::conds
  (s/+ ::cond))

(s/def ::rule
  (s/cat :docstring (s/? string?)
         :salience (s/? (s/keys :req-un [::salience]))
         :conds ::conds
         :arrow #{'=>}
         :effects (s/+ any?)))

(s/def ::query-rhs
  (s/cat
   :arrow #{'=>}
   :returns any?))

(s/def ::query
  (s/cat :docstring (s/? string?)
         :argsv (s/coll-of ?symbol? :kind vector?)
         :conds ::conds
         :rhs (s/? ::query-rhs)))

(defn- parse [spec content]
  (let [res (s/conform spec content)]
    (if (= ::s/invalid res)
      (throw (ex-info (s/explain-str spec content)
                      (s/explain-data spec content)))
      res)))

(defn- cond-kind [[tag m]]
  (if (= tag :fact)
    (if (= (first (:type m)) :simple)
      :simple-fact
      :fact-acc)
    tag))

(defmulti translate
  "Translate rule and query conditions from Claraz syntax to Clara syntax.
   destruct+syms should be a volatile with a collection in it, to which
   vectors of the destructure structure and binding symbol will be added
   for each condition that has a destructuring."
  cond-kind)

(defn- ?symbol [sym]
  (symbol (str '? sym)))

(defn- var-and-arrow [var]
  (when var [var '<-]))

(defn- get-var [var]
  (or var (?symbol (gensym))))

(defn- add-destruct [destruct+syms var destruct]
  (when (and destruct+syms destruct)
    (vswap! destruct+syms conj [(first destruct) var])))

(defmethod translate :simple-fact
  [[_ {:keys [var type destruct exprs]}]]
  (let [var* (get-var var)]
    (->> (concat (var-and-arrow var*) [(val type) destruct] exprs)
      (filter some?)
      vec)))

(defmethod translate :fact-without-var
  [[_ {:keys [type destruct exprs]}]]
    (->> (concat [(val type) destruct] exprs)
      (filter some?)
      vec))

(defmethod translate :fact-acc
  [[_ {:keys [var type destruct exprs]}]]
  (let [var* (get-var var)
        [_ {:keys [acc type]}] type
        acc (or acc (acc/all))]
    (->> (concat (var-and-arrow var*)
                 [acc :from (into (if destruct [type destruct] [type])
                                  exprs)])
      (filter some?)
      vec)))

(defmethod translate :expr [[_ expr]]
  (translate expr))

(defmethod translate :and-or [[_ {:keys [op args]}]]
  (into [op] (mapv translate args)))

(defmethod translate :not-exists [[_ {:keys [op arg]}]]
  [op (translate arg)])

(defmethod translate :test [[_ {:keys [expr]}]]
  [:test expr])

(defn- wrap-in-let [effects destruct+syms]
  `(let [~@(apply concat destruct+syms)] ~@effects))

(defn fact? [x]
  (and (vector? x) (= :fact (first x))))

(defn- add-gensyms-to-facts
  "Add a gensym var to facts that have a destructuring, but no var."
  [conds]
  (walk/postwalk
   (fn [x]
     (if (fact? x)
       (let [[_ {:keys [var destruct]}] x]
         (cond-> x (and destruct (not var))
                 (assoc-in [1 :var] (?symbol (gensym)))))
       x))
   conds))

(defn- get-only-fact-maps
  "Collect only the facts from a nested data structure."
  [x]
  (cond (fact? x) [(second x)]
        (coll? x) (mapcat get-only-fact-maps (filter coll? x))
        :else nil))

(defn- destruct-sym-pairs
  "Returns a list of [destructuring var] vectors from a parsed rule."
  [data]
  (->> (get-only-fact-maps data)
    (map (fn [{:keys [var destruct]}]
           (when destruct
             [(destruct 0) var])))
    (filter some?)))

(defn rule*
  "Function version of claraz.rules/rule."
  [name & body]
  (let [parsed (parse ::rule body)
        {:keys [docstring salience conds effects]} parsed
        conds* (add-gensyms-to-facts conds)
        destruct-syms (destruct-sym-pairs conds*)
        clara-conds (map translate conds*)
        effects* (wrap-in-let effects destruct-syms)
        rule-body (concat (some-> docstring vector)
                          (some-> salience vector)
                          clara-conds
                          ['=> effects*])]
    (dsl/build-rule name rule-body)))

(defmacro rule
  "Create a Clara rule using Claraz syntax. Returns the rule, and does not
   define it in the current namespace.

   Arguments: [name docstring? salience? & body]. Salience is written
   simply :salience n, without a wrapping map.

   Claraz syntax is similar to Clara syntax, the only difference is that
   the <- and :from are not used. Instead of :from Claraz uses a vector.
   These example should be all you need.

   Clara:  [?f <- FactType [destructuring] constraints]
   Claraz: [?f FactType [destructuring] constraints]

   Clara:  [?f <- acc :from [FactType [destructuring] constraints]]
   Claraz: [?f [acc FactType] [destructuring] constraints]].

   The binding symbol (?f above), destructuring vector, and constraints
   are all optional, just like in Clara.

   :not, :and, :or, :exists, and :test conditions are possible, just
   like in Clara.

   Claraz also makes it possible to use symbols bound by destructuring
   in any condition on the left-hand side in the right hand side, even
   if they don't start with a ?. Example:
   [Person [{:keys [name] :as p}]]
   =>
   (insert! (->Fact name p))

   Reusing symbols in destructurings in later conditions shadow earlier
   ones."
  {:style/indent :defn}
  [name & body]
  (apply rule* name body))

(defmacro defrule
  "Essentially like (def name (rule ...). Adds :rule true to the metadata
   of the defined var. See the docstring of claraz.rules/rule for more
   information on how to write rules and queries using the Claraz
   syntax."
  {:style/indent :defn}
  [name & body]
  (let [{:keys [doc] :as r} (apply rule* name body)]
    `(def ~(vary-meta name assoc :rule true :doc doc) ~r)))

(def ^:private queries
  "Used to keep track of queries so that they can be accessed even if they
   are not defined in a namespace."
  (atom {}))

(defn query*
  "Function version of claraz.rules/query."
  [name & body]
  (let [{:keys [docstring argsv conds rhs] :as parsed} (parse ::query body)
        kw-argsv (mapv keyword argsv)
        conds (map translate conds)
        query-body (concat (some-> docstring vector)
                           [kw-argsv]
                           conds)
        query (-> (dsl/build-query name query-body)
                (assoc ::argsv kw-argsv)
                (assoc ::returns (list 'quote (:returns rhs))))]
    query))

(defn save-query [kw query]
  (swap! queries assoc kw query))

(defmacro query
  "Create a Clara query using Claraz syntax. See the docstring of
   claraz.rules/rule."
  {:style/indent :defn}
  [name & body]
  `(let [q# ~(apply query* name body)]
     (save-query ~(keyword name) q#)
     q#))

(defmacro defquery
  "Essentially like (def name (query ...)). Adds :query true to the
   metadata of the defined var. See the docstring of claraz.rules/rule
   for more information on how to write rules and queries using the
   Claraz syntax."
  {:style/indent :defn}
  [name & body]
  (let [q (gensym)]
    `(let [~q ~(apply query* name body)]
       (save-query ~(keyword name) ~q)
       (def ~(vary-meta name assoc :query true :doc (:doc q)) ~q))))

(defn- extract-values [results returns]
  (let [returns* (walk/postwalk #(if (?symbol? %) (keyword %) %) returns)]
    (mapv #(walk/postwalk-replace % returns*) results)))

(defn query+
  "Like clara.rules/query but with two modifications.

   First, query-or-kw can be a keyword naming a query created by
   claraz.rules/query (or query*) and can be used in case the rule is
   not defined in a namespace. The keyword should just be a keyword
   version of the symbol used in the claraz.rules/query call.

   Seconds, args can (but doesn't have to) be passed without the
   keywords, as positional args, e.g. (query+ session some-query 1 2)
   instead of (query+ session some-query :?x 1 :?y 2)."
  [session query-or-kw & args]
  (let [{::keys [returns] :as q} (cond-> query-or-kw
                                   (keyword? query-or-kw) (@queries))
        result (->> (if (and (seq args) (keyword? (first args)))
                      (apply hash-map args)
                      (zipmap (::argsv q) args))
                 (eng/query session q))]
    (cond-> result returns (extract-values returns))))
