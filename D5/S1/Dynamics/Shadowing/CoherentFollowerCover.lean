/- GID: D5/S1/Dynamics/Shadowing/CoherentFollowerCover
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/CoherentFollowerCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-subface followers give coherent finite graphs with onto whole-path bonds. -/

import D5.S1.Dynamics.Shadowing.WholePathProjection
import Mathlib.Data.Stream.Init
import Mathlib.Topology.Constructions
import Mathlib.Topology.Neighborhoods
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

open Set Function Filter Topology

namespace D5.S1.Dynamics.Shadowing.CoherentFollower

universe u v w

abbrev Word (A : Type u) := ℕ → A

/-- Finite concatenation uses the existing stream operation. -/
abbrev prepend {A : Type u} : List A → Word A → Word A := Stream'.appendStream'

private abbrev wordPrefix {A : Type u} (z : Word A) (n : ℕ) := Stream'.take n z

private theorem prepend_append {A : Type u} (u v : List A) (z : Word A) :
    prepend (u ++ v) z = prepend u (prepend v z) := Stream'.append_append_stream u v z

private theorem prepend_drop {A : Type u} (u : List A) (z : Word A) (n : ℕ) :
    prepend u z (u.length + n) = z n := Stream'.get_append_right n u z

private theorem prefix_succ {A : Type u} (z : Word A) (n : ℕ) :
    wordPrefix z (n + 1) = wordPrefix z n ++ [z n] := Stream'.take_succ' n

private theorem prefix_map {A : Type u} {B : Type v} (f : A → B) (z : Word A) (n : ℕ) :
    wordPrefix (fun k => f (z k)) n = (wordPrefix z n).map f :=
  (Stream'.map_take n z f).symm

private theorem prefix_prepend {A : Type u} (u : List A) (z : Word A) (n : ℕ) :
    wordPrefix (prepend u z) (u.length + n) = u ++ wordPrefix z n :=
  (Stream'.append_take n u z).symm

private theorem prepend_prefix_tail {A : Type u} (z : Word A) (n : ℕ) :
    prepend (wordPrefix z n) (fun k => z (n + k)) = z := by
  have ht : (fun k => z (n + k)) = Stream'.drop n z := by
    funext k
    change z (n + k) = z (k + n)
    rw [Nat.add_comm]
  rw [ht]
  exact Stream'.append_take_drop n z

private theorem prepend_prefix_eq {A : Type u} (z t : Word A) {n k : ℕ} (hk : k < n) :
    prepend (wordPrefix z n) t k = z k := by
  have hlen : (wordPrefix z n).length = n := Stream'.length_take n z
  have hk' : k < (wordPrefix z n).length := hlen.symm ▸ hk
  exact (Stream'.get_append_left k (wordPrefix z n) t hk').trans
    (Stream'.take_get k n z hk')

/-- The exact set of continuations of a finite past. -/
def follower {A : Type u} (L : Set (Word A)) (u : List A) : Set (Word A) :=
  {z | prepend u z ∈ L}

/-- Left derivative, with one symbol consumed at time zero. -/
def derivative {A : Type u} (q : Set (Word A)) (a : A) : Set (Word A) :=
  follower q [a]


private theorem follower_append {A : Type u} (L : Set (Word A)) (u v : List A) :
    follower L (u ++ v) = follower (follower L u) v := by
  ext z
  simp only [follower, Set.mem_ofPred, prepend_append]

private theorem follower_cons {A : Type u} (L : Set (Word A)) (a : A) (u : List A) :
    follower L (a :: u) = follower (derivative L a) u := by
  simpa [derivative] using follower_append L [a] u

private theorem derivative_follower {A : Type u} (L : Set (Word A)) (u : List A) (a : A) :
    derivative (follower L u) a = follower L (u ++ [a]) :=
  (follower_append L u [a]).symm

/-- All nonempty followers, with no choice of graph presentation. -/
def Followers {A : Type u} (L : Set (Word A)) :=
  {q : Set (Word A) // ∃ u : List A, q = follower L u ∧ q.Nonempty}

section FiniteFollowers

variable {A : Type u} {V : Type v}

/-- Graph language when initial vertices are restricted to `S`. -/
private def graphFrom (e : V → V → Prop) (ell : V → A) (S : Set V) : Set (Word A) :=
  {z | ∃ p : Word V, p 0 ∈ S ∧ (∀ n, e (p n) (p (n + 1))) ∧
    ∀ n, ell (p n) = z n}

private theorem graphFrom_univ (e : V → V → Prop) (ell : V → A) :
    graphFrom e ell Set.univ = graphLanguage e ell := by
  ext z
  constructor
  · rintro ⟨p, _, he, hl⟩
    exact ⟨p, he, hl⟩
  · rintro ⟨p, he, hl⟩
    exact ⟨p, Set.mem_univ _, he, hl⟩

private def advance (e : V → V → Prop) (ell : V → A) (S : Set V) (a : A) : Set V :=
  {v | ∃ u ∈ S, ell u = a ∧ e u v}

private theorem derivative_graphFrom (e : V → V → Prop) (ell : V → A)
    (S : Set V) (a : A) :
    derivative (graphFrom e ell S) a = graphFrom e ell (advance e ell S a) := by
  ext z
  constructor
  · rintro ⟨p, hS, he, hl⟩
    refine ⟨fun n => p (n + 1), ⟨p 0, hS, hl 0, he 0⟩,
      fun n => he (n + 1), fun n => ?_⟩
    exact hl (n + 1)
  · rintro ⟨p, ⟨v, hv, hla, hve⟩, he, hl⟩
    let q : Word V := fun n => match n with
      | 0 => v
      | n + 1 => p n
    refine ⟨q, hv, ?_, ?_⟩
    · intro n
      cases n with
      | zero => exact hve
      | succ n => exact he n
    · intro n
      cases n with
      | zero => exact hla
      | succ n => exact hl n

private def reachable (e : V → V → Prop) (ell : V → A) : Set V → List A → Set V
  | S, [] => S
  | S, a :: u => reachable e ell (advance e ell S a) u

private theorem follower_graphFrom (e : V → V → Prop) (ell : V → A)
    (S : Set V) (u : List A) :
    follower (graphFrom e ell S) u = graphFrom e ell (reachable e ell S u) := by
  induction u generalizing S with
  | nil => rfl
  | cons a u ih => rw [follower_cons, derivative_graphFrom]; exact ih _

/-- Finite graph presentations have finitely many nonempty followers. -/
theorem finite_followers_of_graph [Finite V] (e : V → V → Prop) (ell : V → A) :
    Finite (Followers (graphLanguage e ell)) := by
  classical
  let T : Set (Set (Word A)) := Set.range (graphFrom e ell)
  have hT : T.Finite := Set.finite_range _
  have hsub : {q : Set (Word A) | ∃ u : List A,
      q = follower (graphLanguage e ell) u ∧ q.Nonempty} ⊆ T := by
    rintro q ⟨u, rfl, _⟩
    refine ⟨reachable e ell Set.univ u, ?_⟩
    rw [← follower_graphFrom, graphFrom_univ]
  exact (hT.subset hsub).to_subtype

/-- The ordinary powerset estimate includes transient and dead vertices. -/
theorem followers_card_le_pow [Fintype V] (e : V → V → Prop) (ell : V → A) :
    Nat.card (Followers (graphLanguage e ell)) ≤ 2 ^ Fintype.card V := by
  classical
  let R := Followers (graphLanguage e ell)
  let f : Set V → Set (Word A) := graphFrom e ell
  let T := Set.range f
  have hT : Finite T := (Set.finite_range f).to_subtype
  let : Finite T := hT
  let j : R → T := fun q => ⟨q.1, by
    obtain ⟨u, hu, _⟩ := q.2
    refine ⟨reachable e ell Set.univ u, ?_⟩
    change graphFrom e ell (reachable e ell Set.univ u) = q.1
    rw [← follower_graphFrom, graphFrom_univ, ← hu]⟩
  have hj : Injective j := by
    intro q r h
    exact Subtype.ext (congrArg (fun x : T => x.1) h)
  let g : Set V → T := fun S => ⟨f S, ⟨S, rfl⟩⟩
  have hg : Surjective g := by
    rintro ⟨q, S, rfl⟩
    exact ⟨S, rfl⟩
  calc
    Nat.card R ≤ Nat.card T := Nat.card_le_card_of_injective j hj
    _ ≤ Nat.card (Set V) := Nat.card_le_card_of_surjective g hg
    _ = 2 ^ Fintype.card V := by simp [Nat.card_eq_fintype_card]

theorem finite_followers_of_sofic {L : Set (Word A)} (h : IsSofic L) :
    Finite (Followers L) := by
  obtain ⟨n, e, ell, rfl⟩ := h
  exact finite_followers_of_graph e ell

#print axioms finite_followers_of_graph
#print axioms followers_card_le_pow
#print axioms finite_followers_of_sofic

end FiniteFollowers

section ClosedFollowers

variable {A : Type u} [TopologicalSpace A]

private theorem continuous_prepend (u : List A) : Continuous (prepend u : Word A → Word A) := by
  induction u with
  | nil => exact continuous_id
  | cons a u ih =>
    apply continuous_pi
    intro n
    cases n with
    | zero => exact continuous_const
    | succ n => exact (continuous_apply n).comp ih

private theorem isClosed_follower {L : Set (Word A)} (h : IsClosed L) (u : List A) :
    IsClosed (follower L u) := h.preimage (continuous_prepend u)

/-- Closedness upgrades extendibility of every wordPrefix to one whole future. -/
private theorem mem_of_all_prefixes {L : Set (Word A)} (hL : IsClosed L) (z : Word A)
    (h : ∀ n, (follower L (wordPrefix z n)).Nonempty) : z ∈ L := by
  classical
  choose t ht using h
  let b : ℕ → Word A := fun n => prepend (wordPrefix z n) (t n)
  have hb : ∀ n, b n ∈ L := ht
  have hlim : Tendsto b atTop (𝓝 z) := by
    apply tendsto_pi_nhds.2
    intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.Ici_mem_atTop (k + 1)] with n hn
    exact (prepend_prefix_eq z (t n) (by have hn' : k + 1 ≤ n := hn; omega)).symm
  exact hL.mem_of_tendsto hlim (Filter.Eventually.of_forall hb)

/-- Forward invariance means removing time zero, with no onto assumption. -/
def ForwardInvariant (L : Set (Word A)) : Prop :=
  ∀ z ∈ L, (fun n => z (n + 1)) ∈ L

omit [TopologicalSpace A] in
private theorem follower_subset {L : Set (Word A)} (hL : ForwardInvariant L) (u : List A) :
    follower L u ⊆ L := by
  induction u with
  | nil => exact Set.Subset.rfl
  | cons a u ih =>
    intro z hz
    apply ih
    exact hL (prepend (a :: u) z) hz

end ClosedFollowers

section CoordinateLanguages

variable {I : Type u} (A : I → Type v)

abbrev Letter (F : Finset I) := (i : {i // i ∈ F}) → A i.1
abbrev ScopedWord (F : Finset I) := Word (Letter A F)

def restrictLetter {F G : Finset I} (h : F ⊆ G) (a : Letter A G) : Letter A F :=
  fun i => a ⟨i.1, h i.2⟩

def restrictWord {F G : Finset I} (h : F ⊆ G) (z : ScopedWord A G) : ScopedWord A F :=
  fun n => restrictLetter A h (z n)





private theorem restrict_prepend {F G : Finset I} (h : F ⊆ G)
    (u : List (Letter A G)) (z : ScopedWord A G) :
    restrictWord A h (prepend u z) =
      prepend (u.map (restrictLetter A h)) (restrictWord A h z) :=
  Stream'.map_append_stream (restrictLetter A h) u z

variable [∀ i, TopologicalSpace (A i)]

/-- The minimal symbolic premises, with finite followers rather than a chosen
graph resolution. `image_eq` is about whole words, not finite marginals. -/
structure LanguageSystem where
  language : (F : Finset I) → Set (ScopedWord A F)
  nonempty : ∀ F, (language F).Nonempty
  closed : ∀ F, IsClosed (language F)
  forward : ∀ F, ForwardInvariant (language F)
  finite_followers : ∀ F, Finite (Followers (language F))
  image_eq : ∀ {F G : Finset I} (h : F ⊆ G),
    restrictWord A h '' language G = language F

namespace LanguageSystem

variable {A}

/-- Soficity supplies the finite-followers premise; no graph is frozen. -/
def ofSofic (L : (F : Finset I) → Set (ScopedWord A F))
    (hn : ∀ F, (L F).Nonempty) (hc : ∀ F, IsClosed (L F))
    (hf : ∀ F, ForwardInvariant (L F)) (hs : ∀ F, IsSofic (L F))
    (hi : ∀ {F G : Finset I} (h : F ⊆ G), restrictWord A h '' L G = L F) :
    LanguageSystem A :=
  ⟨L, hn, hc, hf, fun F => finite_followers_of_sofic (hs F), hi⟩

variable (S : LanguageSystem A)

private theorem project_mem {F G : Finset I} (h : F ⊆ G) {z : ScopedWord A G}
    (hz : z ∈ S.language G) : restrictWord A h z ∈ S.language F := by
  rw [← S.image_eq h]
  exact ⟨z, hz, rfl⟩

private theorem lift_word {F G : Finset I} (h : F ⊆ G) {z : ScopedWord A F}
    (hz : z ∈ S.language F) :
    ∃ w ∈ S.language G, restrictWord A h w = z := by
  rw [← S.image_eq h] at hz
  exact hz

abbrev IsPrefix (F : Finset I) (u : List (Letter A F)) : Prop :=
  (follower (S.language F) u).Nonempty

private theorem project_prefix {F G : Finset I} (h : F ⊆ G) {u : List (Letter A G)}
    (hu : S.IsPrefix G u) : S.IsPrefix F (u.map (restrictLetter A h)) := by
  obtain ⟨z, hz⟩ := hu
  refine ⟨restrictWord A h z, ?_⟩
  change prepend (u.map (restrictLetter A h)) (restrictWord A h z) ∈ S.language F
  rw [← restrict_prepend]
  exact S.project_mem h hz

/-- Every subface is retained; the face type is finite even for arbitrary `I`. -/
abbrev Face (F : Finset I) := {H : Finset I // H ⊆ F}

instance faceFinite (F : Finset I) : Finite (Face F) := by
  classical
  exact Finite.of_injective (fun H : Face F => (⟨H.1, Finset.mem_powerset.mpr H.2⟩ : ↥F.powerset))
    (by intro H K h; exact Subtype.ext (congrArg (fun x : ↥F.powerset => x.1) h))

abbrev topFace (F : Finset I) : Face F := ⟨F, Finset.Subset.refl F⟩

abbrev RawContext (F : Finset I) := (H : Face F) → Set (ScopedWord A H.1)

def vector (F : Finset I) (u : List (Letter A F)) : RawContext (A := A) F :=
  fun H => follower (S.language H.1) (u.map (restrictLetter A H.2))

@[simp] private theorem vector_top (F : Finset I) (u : List (Letter A F)) :
    S.vector F u (topFace F) = follower (S.language F) u := by
  change follower (S.language F) (u.map id) = follower (S.language F) u
  rw [List.map_id]

/-- Only vectors realized by one genuine common finite past are states. -/
def Context (F : Finset I) :=
  {s : RawContext (A := A) F // ∃ u : List (Letter A F), S.IsPrefix F u ∧ s = S.vector F u}

def contextOf (F : Finset I) (u : List (Letter A F)) (hu : S.IsPrefix F u) : S.Context F :=
  ⟨S.vector F u, u, hu, rfl⟩

private theorem component_nonempty {F : Finset I} (s : S.Context F) (H : Face F) :
    (s.1 H).Nonempty := by
  obtain ⟨u, hu, hs⟩ := s.2
  rw [congrFun hs H]
  exact S.project_prefix H.2 hu

def componentFollower {F : Finset I} (s : S.Context F) (H : Face F) :
    Followers (S.language H.1) :=
  ⟨s.1 H, by
    obtain ⟨u, hu, hs⟩ := s.2
    exact ⟨u.map (restrictLetter A H.2), congrFun hs H, S.component_nonempty s H⟩⟩

instance contextFinite (F : Finset I) : Finite (S.Context F) := by
  let : ∀ H : Face F, Finite (Followers (S.language H.1)) :=
    fun H => S.finite_followers H.1
  apply Finite.of_injective (fun s : S.Context F => fun H => S.componentFollower s H)
  intro s t h
  apply Subtype.ext
  funext H
  exact congrArg Subtype.val (congrFun h H)

private theorem vector_snoc (F : Finset I) (u : List (Letter A F)) (a : Letter A F)
    (H : Face F) :
    S.vector F (u ++ [a]) H = derivative (S.vector F u H) (restrictLetter A H.2 a) := by
  simp only [vector, List.map_append, List.map_singleton, derivative_follower]

/-- A current letter must have a whole continuation from the top follower. -/
structure Vertex (F : Finset I) where
  context : S.Context F
  symbol : Letter A F
  allowed : (derivative (context.1 (topFace F)) symbol).Nonempty

@[ext] private theorem vertex_ext {F : Finset I} (v w : S.Vertex F)
    (hc : v.context = w.context) (ha : v.symbol = w.symbol) : v = w := by
  cases v
  cases w
  cases hc
  cases ha
  rfl

instance vertexFinite [∀ i, Finite (A i)] (F : Finset I) : Finite (S.Vertex F) := by
  apply Finite.of_injective (fun v : S.Vertex F => (v.context, v.symbol))
  intro v w h
  exact vertex_ext S v w (congrArg Prod.fst h) (congrArg Prod.snd h)

def label {F : Finset I} (v : S.Vertex F) : Letter A F := v.symbol

/-- Componentwise deterministic derivative, written relationally to avoid
choosing a representative of a context. The next letter is already allowed. -/
def Edge {F : Finset I} (v w : S.Vertex F) : Prop :=
  ∀ H : Face F, w.context.1 H = derivative (v.context.1 H) (restrictLetter A H.2 v.symbol)

def vertexOf (F : Finset I) (u : List (Letter A F)) (a : Letter A F)
    (hu : S.IsPrefix F u) (hua : S.IsPrefix F (u ++ [a])) : S.Vertex F :=
  ⟨S.contextOf F u hu, a, by
    change (derivative (S.vector F u (topFace F)) a).Nonempty
    rw [S.vector_top, derivative_follower]
    exact hua⟩


/-- Whole paths, with every vertex allowed at time zero. -/
def Path (F : Finset I) :=
  {p : ℕ → S.Vertex F // ∀ n, S.Edge (p n) (p (n + 1))}

def pathLabels {F : Finset I} (p : S.Path F) : ScopedWord A F := fun n => (p.1 n).symbol

private theorem prefix_of_word {F : Finset I} {w : ScopedWord A F} (hw : w ∈ S.language F)
    (n : ℕ) : S.IsPrefix F (wordPrefix w n) := by
  refine ⟨fun k => w (n + k), ?_⟩
  change prepend (wordPrefix w n) (fun k => w (n + k)) ∈ S.language F
  rwa [prepend_prefix_tail]

/-- The canonical path after ANY finite past of one whole admitted word. -/
def pathAfter {F : Finset I} (w : ScopedWord A F) (hw : w ∈ S.language F)
    (m : ℕ) : S.Path F := by
  let v : ℕ → S.Vertex F := fun n => S.vertexOf F (wordPrefix w (m + n)) (w (m + n))
    (S.prefix_of_word hw (m + n)) (by
      simpa only [← prefix_succ] using S.prefix_of_word hw (m + n + 1))
  refine ⟨v, fun n => ?_⟩
  intro H
  change S.vector F (wordPrefix w (m + (n + 1))) H =
    derivative (S.vector F (wordPrefix w (m + n)) H) (restrictLetter A H.2 (w (m + n)))
  rw [show m + (n + 1) = m + n + 1 by omega, prefix_succ]
  exact S.vector_snoc F _ _ H

/-- Deterministic reconstruction of every context on an arbitrary graph path.
The initial past `u` need not be empty. -/
private theorem path_context {F : Finset I} (p : S.Path F) (u : List (Letter A F))
    (h0 : (p.1 0).context.1 = S.vector F u) (n : ℕ) :
    (p.1 n).context.1 = S.vector F (u ++ wordPrefix (S.pathLabels p) n) := by
  induction n with
  | zero => change (p.1 0).context.1 = S.vector F (u ++ []); simpa only [List.append_nil] using h0
  | succ n ih =>
    funext H
    rw [p.2 n H, congrFun ih H, prefix_succ, ← List.append_assoc]
    exact (S.vector_snoc F _ _ H).symm

/-- Strong language exactness: the ENTIRE label future remains in the
follower represented by the prescribed initial context. -/
theorem path_in_initial_follower {F : Finset I} (p : S.Path F)
    (u : List (Letter A F)) (h0 : (p.1 0).context.1 = S.vector F u) :
    prepend u (S.pathLabels p) ∈ S.language F := by
  apply mem_of_all_prefixes (isClosed_follower (S.closed F) u) (S.pathLabels p)
  intro n
  have hne := S.component_nonempty (p.1 n).context (topFace F)
  rw [S.path_context p u h0 n, S.vector_top] at hne
  rwa [follower_append] at hne

private theorem path_labels_mem {F : Finset I} (p : S.Path F) :
    S.pathLabels p ∈ S.language F := by
  obtain ⟨u, _, h0⟩ := (p.1 0).context.2
  exact follower_subset (S.forward F) u (S.path_in_initial_follower p u h0)

theorem graphLanguage_exact (F : Finset I) :
    graphLanguage (S.Edge (F := F)) S.label = S.language F := by
  apply Set.Subset.antisymm
  · rintro z ⟨p, he, hl⟩
    have hz := S.path_labels_mem (⟨p, he⟩ : S.Path F)
    have heq : S.pathLabels (⟨p, he⟩ : S.Path F) = z := funext hl
    rwa [heq] at hz
  · intro z hz
    let p := S.pathAfter z hz 0
    refine ⟨p.1, p.2, fun n => ?_⟩
    change z (0 + n) = z n
    rw [Nat.zero_add]

theorem vertex_live {F : Finset I} (v : S.Vertex F) :
    ∃ p : S.Path F, p.1 0 = v := by
  obtain ⟨u, hu, hs⟩ := v.context.2
  obtain ⟨t, ht⟩ := v.allowed
  have hword : prepend (u ++ [v.symbol]) t ∈ S.language F := by
    change prepend [v.symbol] t ∈ v.context.1 (topFace F) at ht
    rw [congrFun hs (topFace F), S.vector_top] at ht
    change prepend u (prepend [v.symbol] t) ∈ S.language F at ht
    rwa [prepend_append]
  let w := prepend (u ++ [v.symbol]) t
  let p := S.pathAfter w hword u.length
  refine ⟨p, vertex_ext S _ _ ?_ ?_⟩
  · apply Subtype.ext
    change S.vector F (wordPrefix w (u.length + 0)) = v.context.1
    have hp : wordPrefix w u.length = u := by
      change wordPrefix (prepend (u ++ [v.symbol]) t) (u.length + 0) = u
      rw [prepend_append]
      simpa only [wordPrefix, Stream'.take_zero, List.append_nil, Nat.add_zero] using
        prefix_prepend u (prepend [v.symbol] t) 0
    rw [Nat.add_zero, hp, ← hs]
  · change w (u.length + 0) = v.symbol
    change prepend (u ++ [v.symbol]) t (u.length + 0) = v.symbol
    rw [prepend_append, prepend_drop]
    rfl

theorem vertex_nonempty (F : Finset I) : Nonempty (S.Vertex F) := by
  obtain ⟨w, hw⟩ := S.nonempty F
  exact ⟨(S.pathAfter w hw 0).1 0⟩

def includeFace {F G : Finset I} (h : F ⊆ G) (H : Face F) : Face G :=
  ⟨H.1, Finset.Subset.trans H.2 h⟩

def restrictRaw {F G : Finset I} (h : F ⊆ G) (s : RawContext (A := A) G) :
    RawContext (A := A) F := fun H => s (includeFace h H)

private theorem restrict_vector {F G : Finset I} (h : F ⊆ G) (u : List (Letter A G)) :
    restrictRaw h (S.vector G u) = S.vector F (u.map (restrictLetter A h)) := by
  funext H
  simp only [restrictRaw, vector, includeFace, List.map_map]
  rfl

def restrictContext {F G : Finset I} (h : F ⊆ G) (s : S.Context G) : S.Context F :=
  ⟨restrictRaw h s.1, by
    obtain ⟨u, hu, hs⟩ := s.2
    exact ⟨u.map (restrictLetter A h), S.project_prefix h hu,
      by rw [hs, S.restrict_vector]⟩⟩

@[simp] private theorem restrictContext_refl (F : Finset I) (s : S.Context F) :
    S.restrictContext (Finset.Subset.refl F) s = s := by
  apply Subtype.ext
  funext H
  rfl

private theorem restrictContext_comp {F G H : Finset I} (hFG : F ⊆ G) (hGH : G ⊆ H)
    (s : S.Context H) :
    S.restrictContext hFG (S.restrictContext hGH s) =
      S.restrictContext (Finset.Subset.trans hFG hGH) s := by
  apply Subtype.ext
  funext K
  rfl

private theorem vertex_snoc_prefix {F : Finset I} (v : S.Vertex F) (u : List (Letter A F))
    (hs : v.context.1 = S.vector F u) : S.IsPrefix F (u ++ [v.symbol]) := by
  have h := v.allowed
  change (derivative (v.context.1 (topFace F)) v.symbol).Nonempty at h
  have heq : v.context.1 (topFace F) = follower (S.language F) u :=
    (congrFun hs (topFace F)).trans (S.vector_top F u)
  change (follower (S.language F) (u ++ [v.symbol])).Nonempty
  rw [heq, derivative_follower] at h
  exact h

/-- Delete coordinates of both the whole face vector and the current letter. -/
def restrictVertex {F G : Finset I} (h : F ⊆ G) (v : S.Vertex G) : S.Vertex F := by
  refine ⟨S.restrictContext h v.context, restrictLetter A h v.symbol, ?_⟩
  obtain ⟨u, hu, hs⟩ := v.context.2
  have hp := S.project_prefix h (S.vertex_snoc_prefix v u hs)
  change (derivative (restrictRaw h v.context.1 (topFace F))
    (restrictLetter A h v.symbol)).Nonempty
  change (derivative ((restrictRaw h v.context.1) (topFace F))
    (restrictLetter A h v.symbol)).Nonempty
  have heq : (restrictRaw h v.context.1) (topFace F) =
      follower (S.language F) (u.map (restrictLetter A h)) := by
    rw [hs, S.restrict_vector]; exact S.vector_top F _
  rw [heq, derivative_follower]
  simpa only [List.map_append, List.map_singleton] using hp

@[simp] theorem restrictVertex_label {F G : Finset I} (h : F ⊆ G) (v : S.Vertex G) :
    S.label (S.restrictVertex h v) = restrictLetter A h (S.label v) := rfl

theorem restrictVertex_edge {F G : Finset I} (h : F ⊆ G) (v w : S.Vertex G)
    (he : S.Edge v w) : S.Edge (S.restrictVertex h v) (S.restrictVertex h w) := by
  intro H
  exact he (includeFace h H)

@[simp] theorem restrictVertex_refl (F : Finset I) (v : S.Vertex F) :
    S.restrictVertex (Finset.Subset.refl F) v = v := by
  apply vertex_ext S
  · exact S.restrictContext_refl F v.context
  · rfl

theorem restrictVertex_comp {F G H : Finset I} (hFG : F ⊆ G) (hGH : G ⊆ H)
    (v : S.Vertex H) :
    S.restrictVertex hFG (S.restrictVertex hGH v) =
      S.restrictVertex (Finset.Subset.trans hFG hGH) v := by
  apply vertex_ext S
  · exact S.restrictContext_comp hFG hGH v.context
  · rfl

def restrictPath {F G : Finset I} (h : F ⊆ G) (p : S.Path G) : S.Path F :=
  ⟨fun n => S.restrictVertex h (p.1 n), fun n => S.restrictVertex_edge h _ _ (p.2 n)⟩

@[simp] theorem restrictPath_refl (F : Finset I) (p : S.Path F) :
    S.restrictPath (Finset.Subset.refl F) p = p := by
  apply Subtype.ext
  funext n
  exact S.restrictVertex_refl F (p.1 n)

theorem restrictPath_comp {F G H : Finset I} (hFG : F ⊆ G) (hGH : G ⊆ H)
    (p : S.Path H) :
    S.restrictPath hFG (S.restrictPath hGH p) =
      S.restrictPath (Finset.Subset.trans hFG hGH) p := by
  apply Subtype.ext
  funext n
  exact S.restrictVertex_comp hFG hGH (p.1 n)

/-- Every ENTIRE prescribed target path lifts, including its arbitrary initial
context. One whole word is lifted BEFORE its past and future are split. -/
theorem restrictPath_surjective {F G : Finset I} (h : F ⊆ G) :
    Surjective (S.restrictPath h) := by
  intro p
  obtain ⟨u, hu, h0⟩ := (p.1 0).context.2
  have hz : prepend u (S.pathLabels p) ∈ S.language F :=
    S.path_in_initial_follower p u h0
  obtain ⟨w, hw, hproj⟩ := S.lift_word h hz
  let q := S.pathAfter w hw u.length
  refine ⟨q, ?_⟩
  apply Subtype.ext
  funext n
  apply vertex_ext S
  · apply Subtype.ext
    change restrictRaw h (S.vector G (wordPrefix w (u.length + n))) = (p.1 n).context.1
    rw [S.restrict_vector, ← prefix_map]
    have hp : (fun k => restrictLetter A h (w k)) = prepend u (S.pathLabels p) := hproj
    rw [hp, prefix_prepend]
    exact (S.path_context p u h0 n).symm
  · change restrictLetter A h (w (u.length + n)) = (p.1 n).symbol
    have heq := congrFun hproj (u.length + n)
    rw [prepend_drop] at heq
    exact heq

/-- Whole-path equality, in the existing graph-language interface. -/
theorem projected_path_language {F G : Finset I} (h : F ⊆ G) :
    graphLanguage (S.Edge (F := G)) (S.restrictVertex h) =
      graphLanguage (S.Edge (F := F)) id := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, he, hr⟩
    refine ⟨p, fun n => ?_, fun _ => rfl⟩
    rw [← hr n, ← hr (n + 1)]
    exact S.restrictVertex_edge h _ _ (he n)
  · rintro p ⟨r, he, hr⟩
    have hp : ∀ n, S.Edge (p n) (p (n + 1)) := by
      intro n
      change ∀ n, r n = p n at hr
      simpa only [hr] using he n
    obtain ⟨q, hq⟩ := S.restrictPath_surjective h (⟨p, hp⟩ : S.Path F)
    refine ⟨q.1, q.2, fun n => ?_⟩
    exact congrFun (congrArg Subtype.val hq) n

/-- Explicit reuse of the pinned finite inverse-system compactness supplier.
The direct whole-word lift above pays its hypothesis for every wordPrefix. -/
theorem every_prefix_lifts [∀ i, Finite (A i)] {F G : Finset I} (h : F ⊆ G) :
    ∀ p ∈ graphLanguage (S.Edge (F := F)) id, ∀ m,
      PrefixLift (S.Edge (F := G)) (S.restrictVertex h) p m :=
  (graphLanguage_eq_iff_prefix_lifts (S.Edge (F := G)) (S.Edge (F := F))
    (S.restrictVertex h) (S.restrictVertex_edge h)).1 (S.projected_path_language h)

/-- The scopewise bound is independent of every later upper challenge. -/
private theorem vertex_card_bound [∀ i, Finite (A i)] (F : Finset I) :
    Nat.card (S.Vertex F) ≤ Nat.card (Letter A F) *
      Nat.card ((H : Face F) → Followers (S.language H.1)) := by
  let : ∀ H : Face F, Finite (Followers (S.language H.1)) :=
    fun H => S.finite_followers H.1
  let j : S.Vertex F → Letter A F × ((H : Face F) → Followers (S.language H.1)) :=
    fun v => (v.symbol, fun H => S.componentFollower v.context H)
  have hj : Injective j := by
    intro v w h
    apply vertex_ext S
    · apply Subtype.ext
      funext H
      exact congrArg Subtype.val (congrFun (congrArg Prod.snd h) H)
    · exact congrArg Prod.fst h
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective j hj

theorem vertex_card_bound_product [∀ i, Finite (A i)] (F : Finset I) :
    letI := Fintype.ofFinite (Face F)
    Nat.card (S.Vertex F) ≤ Nat.card (Letter A F) *
      ∏ H : Face F, Nat.card (Followers (S.language H.1)) := by
  classical
  letI := Fintype.ofFinite (Face F)
  simpa only [Nat.card_pi] using S.vertex_card_bound F

/-- At the empty scope there is exactly one vertex, and its edge is a loop. -/
theorem empty_singleton_loop :
    Nonempty (S.Vertex ∅) ∧ Subsingleton (S.Vertex ∅) ∧
      ∀ v w : S.Vertex ∅, S.Edge v w := by
  classical
  have hword : Subsingleton (ScopedWord A ∅) := inferInstance
  have hL : S.language ∅ = Set.univ := by
    obtain ⟨z, hz⟩ := S.nonempty ∅
    apply Set.eq_univ_of_forall
    intro w
    rwa [Subsingleton.elim w z]
  have hface (H : Face (∅ : Finset I)) : H.1 = ∅ := Finset.subset_empty.1 H.2
  have hcomp (s : S.Context ∅) (H : Face (∅ : Finset I)) : s.1 H = Set.univ := by
    obtain ⟨u, hu, hs⟩ := s.2
    rw [congrFun hs H]
    change follower (S.language H.1) _ = Set.univ
    have hLH : S.language H.1 = Set.univ := by
      have hAll : ∀ K : Finset I, K = ∅ → S.language K = Set.univ := by
        intro K hK
        subst K
        exact hL
      exact hAll H.1 (hface H)
    rw [hLH]
    rfl
  have hctx : Subsingleton (S.Context ∅) := ⟨by
    intro s t
    apply Subtype.ext
    funext H
    rw [hcomp s H, hcomp t H]⟩
  have hvert : Subsingleton (S.Vertex ∅) := ⟨by
    intro v w
    exact vertex_ext S v w (hctx.elim _ _) (Subsingleton.elim _ _)⟩
  refine ⟨S.vertex_nonempty ∅, hvert, ?_⟩
  intro v w H
  rw [hcomp w.context H, hcomp v.context H]
  rfl

/-- The packaged result has no target-equivalent graph or path-lifting premise.
All its data were constructed from the language system. -/
theorem coherent_follower_cover [∀ i, Finite (A i)] :
    (∀ F, Finite (S.Vertex F)) ∧
    (∀ F, Nonempty (S.Vertex F)) ∧
    (∀ F, ∀ v : S.Vertex F, ∃ p : S.Path F, p.1 0 = v) ∧
    (∀ F, graphLanguage (S.Edge (F := F)) S.label = S.language F) ∧
    (∀ {F G : Finset I} (h : F ⊆ G), Surjective (S.restrictPath h)) ∧
    (∀ F, ∀ v : S.Vertex F, S.restrictVertex (Finset.Subset.refl F) v = v) ∧
    (∀ {F G H : Finset I} (hFG : F ⊆ G) (hGH : G ⊆ H) (v : S.Vertex H),
      S.restrictVertex hFG (S.restrictVertex hGH v) =
        S.restrictVertex (Finset.Subset.trans hFG hGH) v) ∧
    (∀ {F G : Finset I} (h : F ⊆ G) (v : S.Vertex G),
      S.label (S.restrictVertex h v) = restrictLetter A h (S.label v)) ∧
    (∀ {F G : Finset I} (h : F ⊆ G) (v w : S.Vertex G),
      S.Edge v w → S.Edge (S.restrictVertex h v) (S.restrictVertex h w)) ∧
    (∀ F, ∀ p : S.Path F, S.restrictPath (Finset.Subset.refl F) p = p) ∧
    (∀ {F G H : Finset I} (hFG : F ⊆ G) (hGH : G ⊆ H) (p : S.Path H),
      S.restrictPath hFG (S.restrictPath hGH p) =
        S.restrictPath (Finset.Subset.trans hFG hGH) p) ∧
    (∀ {F G : Finset I} (h : F ⊆ G),
      ∀ p ∈ graphLanguage (S.Edge (F := F)) id, ∀ m,
        PrefixLift (S.Edge (F := G)) (S.restrictVertex h) p m) ∧
    (∀ F, letI := Fintype.ofFinite (Face F)
      Nat.card (S.Vertex F) ≤ Nat.card (Letter A F) *
        ∏ H : Face F, Nat.card (Followers (S.language H.1))) ∧
    (Nonempty (S.Vertex ∅) ∧ Subsingleton (S.Vertex ∅) ∧
      ∀ v w : S.Vertex ∅, S.Edge v w) := by
  exact ⟨fun F => inferInstance, S.vertex_nonempty, fun _ => S.vertex_live,
    S.graphLanguage_exact, fun h => S.restrictPath_surjective h,
    S.restrictVertex_refl, fun hFG hGH => S.restrictVertex_comp hFG hGH,
    fun h => S.restrictVertex_label h, fun h => S.restrictVertex_edge h,
    S.restrictPath_refl, fun hFG hGH => S.restrictPath_comp hFG hGH,
    fun h => S.every_prefix_lifts h, S.vertex_card_bound_product, S.empty_singleton_loop⟩

#print axioms path_in_initial_follower
#print axioms graphLanguage_exact
#print axioms vertex_live
#print axioms vertex_nonempty
#print axioms restrictVertex_label
#print axioms restrictVertex_edge
#print axioms restrictVertex_refl
#print axioms restrictVertex_comp
#print axioms restrictPath_refl
#print axioms restrictPath_comp
#print axioms restrictPath_surjective
#print axioms projected_path_language
#print axioms every_prefix_lifts
#print axioms vertex_card_bound_product
#print axioms empty_singleton_loop
#print axioms coherent_follower_cover

end LanguageSystem
end CoordinateLanguages

end D5.S1.Dynamics.Shadowing.CoherentFollower
