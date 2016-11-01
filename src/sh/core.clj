(ns ^{:doc "Secret Hitler as a directed multigraph."}
    sh.core
  (:refer-clojure :exclude [count])
  (:require [clojure.java.shell :as sh]
            [faconne.core :as f]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]
            [clojure.core.match :refer [match]]
            [clojure.algo.generic.functor :refer [fmap]]))

;;;;;;;;;;;;
;; Config ;;
;;;;;;;;;;;;

(def game-directory "games/")

;;;;;;;;;;;;;;
;; GraphViz ;;
;;;;;;;;;;;;;;

(defn strike-through
  [thing]
  (let [s (name thing)]
    (apply str (interleave s (repeat (clojure.core/count s) \u0336)))))

(def upper-name (comp clojure.string/upper-case name))

(defn write-attributes
  [attributes]
  (str "["
       (->> (for [[k v] attributes]
              (str (name k) " = " "\"" (name v) "\""))
            (clojure.string/join ", "))
       "]"))

(defn write-edge
  [from to attributes]
  (str (name from) " -> " (name to) (write-attributes attributes) ";"))

(defn write-node
  [node attributes]
  (str (name node) (write-attributes attributes) ";"))

(defn write-graph
  [{:keys [nodes edges]}]
  (str "digraph G {\n"
       "graph [dpi = 450];"
       (->> (mapv (partial apply write-edge) edges)
            (clojure.string/join "\n"))
       (->> (mapv (partial apply write-node) nodes)
            (clojure.string/join "\n"))
       "}"))

(def normalize-policies sort)
(defn policies->label
  [policies]
  (->> (normalize-policies policies)
       (mapv upper-name)
       (clojure.string/join ":")))

(defn turn->attributes
  [{:keys [passed turn policies]}]
  (merge
   (match passed
     :l {:color :blue}
     :f {:color :red}
     :x {:style :dashed} ;; weren't successfully elected
     :v {:color :black}) ;; used veto power
   {:label (str turn ". " (policies->label policies))}))

(defn suspect->attribute
  [faction]
  {:style :filled
   :fillcolor (match faction
                :l :blue
                :f :red
                :not-hitler :green
                :hitler :purple
                _ :white)})

(defn game-graph->graphviz
  [{:keys [nom suspect cap quiz]}]
  (-> {:nodes {} :edges []}
      ;; process nominations
      (update :edges into
              (f/transform nom
                           {president {chancellor [turn]}}
                           [[president chancellor (turn->attributes turn)]]))

      ;; process suspicions
      (update :nodes merge
              (fmap suspect->attribute suspect))

      ;; process caps
      (update :nodes (partial merge-with merge)
              (f/transform cap
                           [{:keys [target]}]
                           {target {:label (strike-through target)}}))
      (update :edges into
              (f/transform cap
                           [{:keys [target president]}]
                           [[president target {:style :dashed :label "BANG!"}]]))

      ;; process quizzes
      (update :edges into
              (f/transform quiz
                           [{:keys [president target claim]}]
                           [[president target {:style :dashed
                                               :label (str (upper-name claim) "?")}]]))))

(defn troll-braden
  [graphviz]
  (let [replacement-name
        (rand-nth
         ["baden" "branden" "bronden" "broden" "brandon"])]
    (clojure.string/replace graphviz #"braden" replacement-name)))

(defn graphviz->png
  [graphviz out-name]
  (let [tmp ".eek-barba-durkel.tmp"]
    (spit tmp graphviz)
    (sh/sh "dot" "-T" "png" tmp "-o" out-name)))

(defn render
  [game-graph out]
  (-> game-graph
      game-graph->graphviz
      write-graph
      troll-braden
      (graphviz->png out)))

;;;;;;;;;;;;;;;;;;;;;;;
;; Interactive Games ;;
;;;;;;;;;;;;;;;;;;;;;;;

;; a game is a doubly linked list zipper of actions
(def empty-game [[] '()])

(defn undo
  ([[accepted undone]]
   (if (empty? accepted)
     [accepted undone]
     [(pop accepted)
      (conj undone (peek accepted))]))
  ([game times]
   (first (drop times (iterate undo game)))))

(defn redo
  ([[accepted [next & rest]]]
   (if-not next
     [accepted '()]
     [(conj accepted next) rest]))
  ([game times]
   (first (drop times (iterate redo game)))))

(defn act
  [[accepted _] action]
  [(conj accepted action) '()])

(defn view
  ([f [accepted _]]
   (f accepted))
  ([f]
   #(view f %)))

(defn nom
  [game president chancellor policies passed]
  (act game {:type :nom
             :president president, :chancellor chancellor
             :policies policies, :passed passed}))

(defn suspect
  [game person & [faction]]
  (act game {:type :suspect, :person person, :faction faction}))

(defn cap
  [game president target]
  (act game {:type :cap, :president president, :target target}))

(defn quiz
  [game president target claim]
  (act game {:type :quiz, :president president, :target target, :claim claim}))

(def fold-actions
  (view (fn [accepted]
          (-> (group-by :type accepted)
              (update :nom (partial map-indexed #(assoc %2 :turn %1)))
              (update :nom
                      (f/transformer
                       [{:keys [president chancellor] :as turn}]
                       {president {chancellor [turn]}}))
              (update :suspect
                      #(reduce (fn [acc {:keys [person faction]}]
                                 (assoc acc person faction))
                               {}
                               %))))))

(defn count-policies
  "Maybe the ugliest Clojure I've written in the past year.
  Card counting is surprisingly difficult.

  This doesn't even handle vetos or random policies."
  [noms]
  (let [full-deck {:l 6,:f 11}
        empty-deck {:l 0 :f 0}
        total #(+ (:l %) (:f %))
        invert #(case % :l :f :f :l)]

    (letfn [(buried-policies [remaining]
              ;; if there's a negative number of fascists remaining,
              ;; that means liberals were buried.
              (->> (concat (repeat (* -1 (:f remaining)) :f)
                           (repeat (* -1 (:l remaining)) :l))
                   (mapv invert)
                   frequencies))

            (invert-buried [buried]
              (->> buried (mapv (fn [[k v]] [(invert k) v])) (into {})))

            (adjust-remaining-to-account-for-buried
              [remaining buried]
              (as-> remaining $
                (merge-with + $ (invert-buried buried))
                (merge-with - $ buried)))

            (adjust-discarded-to-account-for-buried
              [discarded buried]
              (as-> discarded $
                (merge-with + $ buried)
                (merge-with - $ (invert-buried buried))))

            (update-decks [decks remaining discarded buried]
              (-> decks
                  (assoc :remaining (adjust-remaining-to-account-for-buried remaining buried)
                         :discarded discarded)
                  (update :buried #(merge-with + % buried))))


            (process-nom [{:keys [discarded remaining] :as decks}
                          {:keys [policies passed]}]

              (if (< (total remaining) 3)
                ;; p1,p2 come from remaining; p3 from discarded
                ;; only if nothing has been discarded. If things have,
                ;; gotta use something like (take (total remaining) policies).
                ;; or a split?
                (let [[p1 p2 p3] policies
                      ;; carryover buries from last of
                      ;; remaining deck
                      carry-over-buries
                      (buried-policies
                       (->> (frequencies [p1 p2])
                            (merge-with - remaining)))

                      remaining' (-> discarded
                                     (adjust-discarded-to-account-for-buried carry-over-buries)
                                     (update p3 dec))
                      discarded' (-> (frequencies policies)
                                     (update passed dec))
                      buried (merge-with + carry-over-buries
                                         ;; buries after recyling discarded
                                         (buried-policies remaining'))]
                  (update-decks decks remaining' discarded' buried))

                (let [freqs (frequencies policies)
                      remaining' (merge-with - remaining freqs)
                      discarded' (-> (merge-with + discarded freqs)
                                     (update passed dec))
                      buried (buried-policies remaining')]
                  (update-decks decks remaining' discarded' buried))))]

      (let [{:keys [remaining discarded] :as decks}
            (reduce process-nom
                    {:remaining full-deck
                     :discarded empty-deck}
                    noms)]
        (if (< (total remaining) 3)
          (merge decks
                 {:discarded empty-deck
                  :remaining (merge-with + remaining discarded)
                  :top-two remaining})
          decks)))))

;; (count-policies
;;  [{:policies [:f :f :l] :passed :l}
;;   {:policies [:f :f :l] :passed :l}
;;   {:policies [:f :f :l] :passed :l}
;;   {:policies [:f :f :f] :passed :f} ;; buried :l
;;   {:policies [:f :l :l] :passed :l}
;;   ;; 1 :l, :1 :f remaining
;;   {:policies [:f :f :f] :passed :f}
;;   ;; {:policies [:f :f :f] :passed :f}
;;   ])


(def remaining-policies
  (view (fn [accepted] (count-policies (:nom (group-by :type accepted))))))

;;;;;;;;;;;
;; State ;;
;;;;;;;;;;;

(def game-state (atom empty-game))

(defn begin-game!
  []
  (let [format (java.text.SimpleDateFormat. "yyyy-MM-dd_HH:mm:ss")
        prefix (str game-directory (.format format (java.util.Date.)))
        game-data-file (str prefix ".edn")
        png (str prefix ".png")]
    (io/make-parents game-data-file)
    (reset! game-state empty-game)
    (add-watch game-state :renderer
               (fn [_ _ _ new-state]
                 (spit game-data-file
                       (with-out-str (pprint/pprint new-state)))
                 (render (fold-actions new-state) png)))
    (render (fold-actions empty-game) png)
    (future (sh/sh "eog" png))
    nil))

(defn statefully
  [f & [and-then]]
  (fn [& args]
    (swap! game-state #(apply f % args))
    (if and-then (and-then) nil)))

(defn view-state
  [f]
  (fn [& args] (apply f @game-state args)))

(def count (view-state remaining-policies))
(def nom! (statefully nom count))
(def undo! (statefully undo))
(def redo! (statefully redo))
(def cap! (statefully cap))
(def quiz! (statefully quiz))
(def suspect! (statefully suspect))

(defn end-game!
  []
  (remove-watch game-state :renderer)
  (reset! game-state empty-game)
  nil)
