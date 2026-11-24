/- GID: D5/S0/Automata/FernauRystsovShortestResetPrefix
   generality: I
   mirror-B: D5/B/S0/Automata/FernauRystsovShortestResetPrefix
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Automata/FernauRystsovShortestResetPrefix.claim; result=D5/S0/Automata/FernauRystsovShortestResetPrefix.result; claim=D5/S0/Automata/FernauRystsovShortestResetPrefix.claim
   digest: Refutes optimality of the shortest-first strategy for DFA product resets. -/

import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn

/-! # Shortest reset prefixes in a shared-letter product -/

set_option autoImplicit false

universe u v v'

namespace D5.S0.Automata.FernauRystsovShortestResetPrefix

private def Reset {α σ : Type*} (A : DFA α σ) (w : List α) : Prop :=
  ∀ p q, A.evalFrom p w = A.evalFrom q w

private def Short {α σ : Type*} (A : DFA α σ) (w : List α) : Prop :=
  Reset A w ∧ ∀ x, Reset A x → w.length ≤ x.length

/-- The optimal-length reading of Fernau and Rystsov's fourth question in §7. -/
def claim : Prop :=
  ∀ k m n : ℕ, 0 < k → 0 < m → 0 < n →
    ∀ (A : DFA (Fin k) (Fin m)) (B : DFA (Fin k) (Fin n)),
      (∃ r, Reset A r) → (∃ r, Reset B r) →
      ∃ u v : List (Fin k), Short A u ∧ Short (A.inter B) (u ++ v)

private def WordImage {α σ : Type*} (A : DFA α σ) (S : Set σ) (w : List α) : Set σ :=
  (fun p => A.evalFrom p w) '' S

private def ResetsOn {α σ : Type*} (A : DFA α σ) (S : Set σ) (w : List α) : Prop :=
  ∃ p, WordImage A S w = {p}

private def ShortestOn {α σ : Type*} (A : DFA α σ) (S : Set σ) (w : List α) : Prop :=
  ResetsOn A S w ∧ ∀ x, ResetsOn A S x → w.length ≤ x.length

private theorem reset_iff_resetsOn_univ {α σ : Type*} [Nonempty σ]
    (A : DFA α σ) (w : List α) : Reset A w ↔ ResetsOn A Set.univ w := by
  simp only [ResetsOn, WordImage, Set.image_univ, Set.range_eq_singleton_iff]
  constructor
  · intro h
    exact ⟨A.evalFrom A.start w, fun p => h p A.start⟩
  · rintro ⟨_, h⟩ p q
    exact (h p).trans (h q).symm

private theorem short_iff_shortestOn_univ {α σ : Type*} [Nonempty σ]
    (A : DFA α σ) (w : List α) : Short A w ↔ ShortestOn A Set.univ w := by
  simp only [Short, ShortestOn, reset_iff_resetsOn_univ]

private theorem eval_inter {α : Type u} {σ τ : Type v} (A : DFA α σ) (B : DFA α τ)
    (p : σ) (q : τ) (w : List α) :
    (A.inter B).evalFrom (p, q) w = (A.evalFrom p w, B.evalFrom q w) := by
  induction w generalizing p q with
  | nil => rfl
  | cons a w ih => simpa only [DFA.evalFrom_cons, DFA.inter_step] using ih (A.step p a) (B.step q a)

private theorem reset_inter_iff {α : Type u} {σ τ : Type v} (A : DFA α σ) (B : DFA α τ)
    (w : List α) : Reset (A.inter B) w ↔ Reset A w ∧ Reset B w := by
  constructor
  · intro h
    constructor
    · intro p q
      simpa only [eval_inter] using congrArg Prod.fst (h (p, B.start) (q, B.start))
    · intro p q
      simpa only [eval_inter] using congrArg Prod.snd (h (A.start, p) (A.start, q))
  · rintro ⟨hA, hB⟩ ⟨p, q⟩ ⟨p', q'⟩
    rw [eval_inter, eval_inter, hA p p', hB q q']

private theorem reset_inter_append_iff {α : Type u} {σ τ : Type v} [Nonempty τ]
    {A : DFA α σ} {B : DFA α τ} {u : List α} (hu : Reset A u) (v : List α) :
    Reset (A.inter B) (u ++ v) ↔ ResetsOn B (WordImage B Set.univ u) v := by
  have hu' : Reset A (u ++ v) := by
    intro p q
    rw [DFA.evalFrom_of_append, DFA.evalFrom_of_append, hu p q]
  have image_append : WordImage B (WordImage B Set.univ u) v =
      WordImage B Set.univ (u ++ v) := by
    simp only [WordImage, Set.image_image, DFA.evalFrom_of_append]
  rw [reset_inter_iff, and_iff_right hu', reset_iff_resetsOn_univ]
  simp only [ResetsOn, image_append]

private def Staged {α : Type u} {σ τ : Type v} (A : DFA α σ) (B : DFA α τ) : Prop :=
  ∃ u v : List α, ShortestOn A Set.univ u ∧
    ShortestOn B (WordImage B Set.univ u) v ∧ ShortestOn (A.inter B) Set.univ (u ++ v)

private theorem staged_iff_prefix {α : Type u} {σ τ : Type v} [Nonempty σ] [Nonempty τ]
    (A : DFA α σ) (B : DFA α τ) :
    Staged A B ↔ ∃ u v : List α, Short A u ∧ Short (A.inter B) (u ++ v) := by
  constructor
  · rintro ⟨u, v, hA, _, hProd⟩
    exact ⟨u, v, (short_iff_shortestOn_univ A u).mpr hA,
      (short_iff_shortestOn_univ (A.inter B) (u ++ v)).mpr hProd⟩
  · rintro ⟨u, v, hA, hProd⟩
    refine ⟨u, v, (short_iff_shortestOn_univ A u).mp hA, ⟨?_, ?_⟩,
      (short_iff_shortestOn_univ (A.inter B) (u ++ v)).mp hProd⟩
    · exact (reset_inter_append_iff hA.1 v).mp hProd.1
    · intro z hz
      have bound := hProd.2 (u ++ z) ((reset_inter_append_iff hA.1 z).mpr hz)
      simpa only [List.length_append, Nat.add_le_add_iff_left] using bound

private def relabel {α β σ τ : Type*} (e : α ≃ β) (f : σ ≃ τ) (A : DFA α σ) : DFA β τ :=
  DFA.reindex f (A.comap e.symm)

private theorem eval_relabel {α β σ τ : Type*} (e : α ≃ β) (f : σ ≃ τ)
    (A : DFA α σ) (p : σ) (w : List α) :
    (relabel e f A).evalFrom (f p) (w.map e) = f (A.evalFrom p w) := by
  simp [relabel, List.map_map, Function.comp_def]

private theorem reset_relabel_iff {α β σ τ : Type*} (e : α ≃ β) (f : σ ≃ τ)
    (A : DFA α σ) (w : List α) :
    Reset (relabel e f A) (w.map e) ↔ Reset A w := by
  constructor
  · intro h p q
    apply f.injective
    simpa only [eval_relabel] using h (f p) (f q)
  · intro h p q
    obtain ⟨p, rfl⟩ := f.surjective p
    obtain ⟨q, rfl⟩ := f.surjective q
    rw [eval_relabel, eval_relabel, h p q]

private theorem short_relabel_iff {α β σ τ : Type*} (e : α ≃ β) (f : σ ≃ τ)
    (A : DFA α σ) (w : List α) :
    Short (relabel e f A) (w.map e) ↔ Short A w := by
  unfold Short
  rw [reset_relabel_iff]
  simp only [List.length_map]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · intro h x hx
    simpa only [List.length_map] using h (x.map e) ((reset_relabel_iff e f A x).mpr hx)
  · intro h x hx
    obtain ⟨x, rfl⟩ := List.map_surjective_iff.mpr e.surjective x
    simpa only [List.length_map] using h x ((reset_relabel_iff e f A x).mp hx)

private theorem relabel_inter {α β : Type*} {σ τ : Type v} {σ' τ' : Type v'}
    (e : α ≃ β) (f : σ ≃ σ') (g : τ ≃ τ') (A : DFA α σ) (B : DFA α τ) :
    (relabel e f A).inter (relabel e g B) = relabel e (Equiv.prodCongr f g) (A.inter B) := rfl

private def SourceClaim : Prop :=
  ∀ (α σ τ : Type) [Fintype α] [Fintype σ] [Fintype τ]
    [Nonempty α] [Nonempty σ] [Nonempty τ]
    (A : DFA α σ) (B : DFA α τ),
      (∃ r, ResetsOn A Set.univ r) → (∃ r, ResetsOn B Set.univ r) → Staged A B

private theorem source_claim_iff : claim ↔ SourceClaim := by
  constructor
  · intro h α σ τ _ _ _ _ _ _ A B hA hB
    let e := Fintype.equivFin α
    let f := Fintype.equivFin σ
    let g := Fintype.equivFin τ
    obtain ⟨r, hr⟩ := hA
    obtain ⟨s, hs⟩ := hB
    obtain ⟨u, v, hu, huv⟩ := h _ _ _ Fintype.card_pos Fintype.card_pos Fintype.card_pos
      (relabel e f A) (relabel e g B)
      ⟨r.map e, (reset_relabel_iff e f A r).mpr ((reset_iff_resetsOn_univ A r).mpr hr)⟩
      ⟨s.map e, (reset_relabel_iff e g B s).mpr ((reset_iff_resetsOn_univ B s).mpr hs)⟩
    obtain ⟨u, rfl⟩ := List.map_surjective_iff.mpr e.surjective u
    obtain ⟨v, rfl⟩ := List.map_surjective_iff.mpr e.surjective v
    apply (staged_iff_prefix A B).mpr
    refine ⟨u, v, (short_relabel_iff e f A u).mp hu, ?_⟩
    apply (short_relabel_iff e (Equiv.prodCongr f g) (A.inter B) (u ++ v)).mp
    rwa [← relabel_inter, List.map_append]
  · intro h k m n hk hm hn A B hA hB
    let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨r, hr⟩ := hA
    obtain ⟨s, hs⟩ := hB
    exact (staged_iff_prefix A B).mp (h (Fin k) (Fin m) (Fin n) A B
      ⟨r, (reset_iff_resetsOn_univ A r).mp hr⟩ ⟨s, (reset_iff_resetsOn_univ B s).mp hs⟩)

private def first : DFA (Fin 2) (Fin 3) where
  step p a := if a = 0 then (if p = 2 then 1 else 0) else p + 1
  start := 0
  accept := ∅

private def second : DFA (Fin 2) (Fin 4) where
  step p a :=
    if a = 0 then
      match p.val with
      | 0 | 1 => 1
      | 2 => 2
      | _ => 0
    else
      match p.val with
      | 1 => 2
      | 2 => 3
      | _ => 0
  start := 0
  accept := ∅

private local instance {α σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : DFA α σ) (w : List α) : Decidable (Reset A w) :=
  inferInstanceAs (Decidable (∀ p q, A.evalFrom p w = A.evalFrom q w))

private def a : Fin 2 := 0
private def b : Fin 2 := 1

private def firstLayer (n : ℕ) : List (List (Fin 2)) :=
  match n with
  | 2 => [[a, a]]
  | 3 => [[a, a, a], [a, a, b], [b, a, a]]
  | 4 => [[a, a, a, a], [a, a, a, b], [a, a, b, a], [a, a, b, b],
          [a, b, a, a], [b, a, a, a], [b, a, a, b], [b, b, a, a]]
  | _ => []

private def secondLayer (n : ℕ) : List (List (Fin 2)) :=
  match n with
  | 3 => [[b, b, b]]
  | 4 => [[a, b, b, b], [b, b, a, a], [b, b, b, a], [b, b, b, b]]
  | _ => []

private def productLayer (n : ℕ) : List (List (Fin 2)) :=
  if n = 4 then [[b, b, a, a]] else []

private def HasResetLayers (A : DFA (Fin 2) (Fin 3)) (B : DFA (Fin 2) (Fin 4))
    (w : List (Fin 2)) (n : ℕ) : Prop :=
  (Reset A w ↔ w ∈ firstLayer n) ∧
  (Reset B w ↔ w ∈ secondLayer n) ∧
  (Reset (A.inter B) w ↔ w ∈ productLayer n)

private local instance (A : DFA (Fin 2) (Fin 3)) (B : DFA (Fin 2) (Fin 4))
    (w : List (Fin 2)) (n : ℕ) : Decidable (HasResetLayers A B w n) := by
  unfold HasResetLayers
  infer_instance

private theorem reset_layers (w : List (Fin 2)) (hw : w.length ≤ 4) :
    HasResetLayers first second w w.length := by
  have rows : ∀ (n : Fin 5) (f : Fin n.val → Fin 2),
      HasResetLayers first second (List.ofFn f) n.val := by decide
  simpa only [List.ofFn_get] using rows ⟨w.length, Nat.lt_succ_of_le hw⟩ w.get

private theorem mem_firstLayer_of_le_two {w : List (Fin 2)} (hw : w.length ≤ 2)
    (hm : w ∈ firstLayer w.length) : w = [a, a] := by
  have cases : w.length = 0 ∨ w.length = 1 ∨ w.length = 2 := by omega
  rcases cases with h | h | h
  · simp [h, firstLayer] at hm
  · simp [h, firstLayer] at hm
  · simpa [h, firstLayer] using hm

/-- In the three-by-four product the respective unique optima begin with different letters. -/
theorem result : ¬ claim := by
  intro h
  have firstReset : Reset first [a, a] :=
    (reset_layers [a, a] (by decide)).1.mpr (by decide)
  have secondReset : Reset second [b, b, b] :=
    (reset_layers [b, b, b] (by decide)).2.1.mpr (by decide)
  have productReset : Reset (first.inter second) [b, b, a, a] :=
    (reset_layers [b, b, a, a] (by decide)).2.2.mpr (by decide)
  have firstSingleton := (reset_iff_resetsOn_univ first _).mp firstReset
  have secondSingleton := (reset_iff_resetsOn_univ second _).mp secondReset
  obtain ⟨u, v, huSource, _, huvSource⟩ :=
    source_claim_iff.mp h (Fin 2) (Fin 3) (Fin 4) first second
      ⟨_, firstSingleton⟩ ⟨_, secondSingleton⟩
  have hu := (short_iff_shortestOn_univ first u).mpr huSource
  have huv := (short_iff_shortestOn_univ (first.inter second) (u ++ v)).mpr huvSource
  have huLength : u.length ≤ 2 := hu.2 _ firstReset
  have huvLength : (u ++ v).length ≤ 4 := huv.2 _ productReset
  have huWord : u = [a, a] :=
    mem_firstLayer_of_le_two huLength ((reset_layers u (by omega)).1.mp hu.1)
  have huvWord : u ++ v = [b, b, a, a] := by
    have hm := (reset_layers (u ++ v) huvLength).2.2.mp huv.1
    by_cases hl : (u ++ v).length = 4
    · simpa only [productLayer, hl, if_true, List.mem_singleton] using hm
    · simp only [productLayer, hl, if_false, List.not_mem_nil] at hm
  subst u
  have heads := congrArg List.head? huvWord
  change some a = some b at heads
  exact (by decide : a ≠ b) (Option.some.inj heads)

end D5.S0.Automata.FernauRystsovShortestResetPrefix
