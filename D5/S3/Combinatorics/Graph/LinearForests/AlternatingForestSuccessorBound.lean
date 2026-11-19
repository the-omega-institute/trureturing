/- GID: D5/S3/Combinatorics/Graph/LinearForests/AlternatingForestSuccessorBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/AlternatingForestSuccessorBound
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: The remaining head counts bound connector probabilities in an alternating forest. -/

import D5.S3.Combinatorics.Graph.LinearForests.AlternatingSuccessorSetBound

/-! A bound on the next connector in an oriented alternating forest completion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Combinatorics.Graph.LinearForests
open CompatibleCycleInventory DirectedForestCompletion AlternatingSuccessorSetBound Relation
open Equiv
open scoped ENNReal

namespace D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound

variable {V : Type*} [Finite V]

private theorem complete_of_cycle {V : Type*} [Finite V] (E : V → V → Prop)
    (σ : Perm V) (full : σ.IsCycleOn Set.univ)
    (hedge : ∀ a b, E a b → σ a = b) {v : V}
    (hv : TransGen E v v) : ∀ a, E a (σ a) := by
  have step (a : V) (ha : TransGen E a v) : E a (σ a) ∧ TransGen E (σ a) v := by
    obtain ⟨b, he, hp⟩ := TransGen.head'_iff.mp ha
    have hb := hedge a b he
    subst b
    refine ⟨he, ?_⟩
    rcases hp.cases_head with h | ⟨c, hc, ht⟩
    · exact h ▸ hv
    · exact TransGen.head' hc ht
  have loop (i : ℕ) : TransGen E ((σ ^ i) v) v := by
    induction i with
    | zero => simpa using hv
    | succ i ih =>
      rw [pow_succ', Perm.mul_apply]
      exact (step _ ih).2
  intro a
  obtain ⟨i, rfl⟩ := (full.2 (Set.mem_univ v) (Set.mem_univ a)).exists_nat_pow_eq
  exact (step _ (loop i)).1

private theorem partial_cycle_acyclic {V : Type*} [Finite V] (E : V → V → Prop)
    (σ : Perm V) (full : σ.IsCycleOn Set.univ)
    (hedge : ∀ a b, E a b → σ a = b)
    (hsparse : Nat.card {p : V × V // E p.1 p.2} < Nat.card V) :
    ∀ v, ¬ TransGen E v v := by
  intro v hcycle
  let f (a : V) : {p : V × V // E p.1 p.2} :=
    ⟨(a, σ a), complete_of_cycle E σ full hedge hcycle a⟩
  have hinj : Function.Injective f := fun _ _ h => congrArg (fun p => p.val.1) h
  exact (not_le_of_gt hsparse) (Nat.card_le_card_of_injective f hinj)

private theorem heads_card_ge (E : V → V → Prop) (k : V → Bool) (b : Bool) :
    Nat.card (Side k b) - Nat.card {p : V × V // E p.1 p.2} ≤
      Nat.card {x : Head E // k x = b} := by
  classical
  let seen : Set V := {y | ∃ x, E x y}
  let color : Set V := {v | k v = b}
  let target : {p : V × V // E p.1 p.2} → seen :=
    fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
  have hSeen : seen.ncard ≤ Nat.card {p : V × V // E p.1 p.2} := by
    apply Nat.card_le_card_of_surjective target
    rintro ⟨v, x, h⟩
    exact ⟨⟨(x,v), h⟩, rfl⟩
  let equiv : {x : Head E // k x = b} ≃ ↥(color \ seen) :=
    { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr equiv]
  change color.ncard - Nat.card {p : V × V // E p.1 p.2} ≤ (color \ seen).ncard
  exact (Nat.sub_le_sub_left hSeen _).trans (Set.le_ncard_sdiff seen color)

/-- The prescribed edges leave at least `n - |E|` heads of each color. -/
theorem mass_of_successor_components (E : V → V → Prop) (k : V → Bool) (n : ℕ)
    (h0 : Nat.card (Side k false) = n) (h1 : Nat.card (Side k true) = n)
    (hsize : Nat.card {p : V × V // E p.1 p.2} + 2 ≤ n)
    (μ : PMF (AlternatingCompletion E k))
    (hμ : ∀ σ, μ σ = (Nat.card (AlternatingCompletion E k) : ℝ≥0∞)⁻¹) :
    ∃ (t : Component E ≃ Tail E) (h : Component E ≃ Head E),
      (∀ A, Quotient.mk (EqvGen.setoid E) (t A).1 = A) ∧
      (∀ A, Quotient.mk (EqvGen.setoid E) (h A).1 = A) ∧
      ∀ (A : Component E) (targets : Finset (Component E)), A ∉ targets →
        let targetCount := targets.card
        μ.toOuterMeasure {σ | ∃ B ∈ targets, σ.1 (t A) = (h B).1} ≤
          (targetCount : ℝ≥0∞) /
            ((n - Nat.card {p : V × V // E p.1 p.2} - 1 : ℕ) : ℝ≥0∞) := by
  classical
  obtain ⟨ref, _⟩ := μ.support_nonempty
  have hout : Relator.RightUnique E := fun {_ _ _} ha hb =>
    (ref.2.2.2.1 _ _ ha).symm.trans (ref.2.2.2.1 _ _ hb)
  have hin : Relator.LeftUnique E := fun {_ _ _} ha hb =>
    ref.1.injective ((ref.2.2.2.1 _ _ ha).trans (ref.2.2.2.1 _ _ hb).symm)
  have halt (a b : V) (he : E a b) : k a ≠ k b := by
    rw [← ref.2.2.2.1 a b he]
    exact (ref.2.2.2.2 a).symm
  have hsparse : Nat.card {p : V × V // E p.1 p.2} < Nat.card V :=
    lt_of_lt_of_le (by omega : Nat.card {p : V × V // E p.1 p.2} < n)
      (h0 ▸ Nat.card_le_card_of_injective (fun x : Side k false => x.1) Subtype.val_injective)
  have hacyclic := partial_cycle_acyclic E ref.1 ref.2.2.1 ref.2.2.2.1 hsparse
  obtain ⟨t, h, Φ, ht, hh, hΦ, _⟩ :=
    alternating_completion_classification n E k hout hin hacyclic halt h0 h1
  let s : Component E → Bool := fun A => k (h A)
  let d : Component E → Bool := fun A => !(k (t A))
  let K := Compatible s d
  let ν : PMF K := μ.map Φ
  have hν (σ : K) : ν σ = (Nat.card K : ℝ≥0∞)⁻¹ := by
    rw [← Nat.card_congr Φ]
    change (μ.map Φ) σ = _
    rw [PMF.map_apply]
    have he (a : AlternatingCompletion E k) : σ = Φ a ↔ a = Φ.symm σ := by
      constructor
      · intro he
        exact (Φ.symm_apply_apply a).symm.trans (congrArg Φ.symm he).symm
      · intro he
        rw [he, Φ.apply_symm_apply]
    simp only [he, tsum_ite_eq]
    exact hμ _
  have side_ge (b : Bool) :
      n - Nat.card {p : V × V // E p.1 p.2} ≤ Nat.card (Side s b) := by
    have cardColor : Nat.card (Side k b) = n := by cases b <;> assumption
    have hs : Nat.card (Side s b) = Nat.card {x : Head E // k x = b} :=
      Nat.card_congr (Equiv.subtypeEquiv h (fun _ => Iff.rfl))
    rw [hs, ← cardColor]
    exact heads_card_ge E k b
  have hcolors (b : Bool) : 2 ≤ Nat.card (Side s b) := by
    have := side_ge b
    omega
  refine ⟨t, h, ht, hh, ?_⟩
  intro A targets hA
  have he :
      {σ : AlternatingCompletion E k | ∃ B ∈ targets, σ.1 (t A) = (h B).1} =
        Φ ⁻¹' {σ : K | σ.1 A ∈ targets} := by
    ext σ
    change (∃ B ∈ targets, σ.1 (t A) = (h B).1) ↔ (Φ σ).1 A ∈ targets
    rw [hΦ]
    constructor
    · intro hs
      obtain ⟨B, hB, he⟩ := hs
      have he' : (Φ σ).1 A = B := h.injective (Subtype.ext he)
      exact he'.symm ▸ hB
    · intro hs
      exact ⟨_, hs, rfl⟩
  rw [he, ← PMF.toOuterMeasure_map_apply Φ μ]
  exact (successor_set_mass_le s d A targets hA hcolors ν hν).trans
    (ENNReal.div_le_div_left (Nat.cast_le.mpr (Nat.sub_le_sub_right (side_ge (d A)) 1)) _)

end D5.S3.Combinatorics.Graph.LinearForests.AlternatingForestSuccessorBound
