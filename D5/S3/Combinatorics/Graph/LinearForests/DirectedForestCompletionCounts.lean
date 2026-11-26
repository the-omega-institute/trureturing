/- GID: D5/S3/Combinatorics/Graph/LinearForests/DirectedForestCompletionCounts
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/DirectedForestCompletionCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Edge cardinality and the exact uniform extension mass of a directed linear forest. -/

import D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion

/-! Exact counting on the original labelled vertices and full cycles. -/

namespace D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletionCounts

open Relation
open DirectedForestCompletion
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf uniformPmf_toOuterMeasure_apply)
open scoped ENNReal

variable {V : Type*}

private noncomputable def edgeSourceEquiv (E : V → V → Prop) (hout : Relator.RightUnique E) :
    {xy : V × V // E xy.1 xy.2} ≃ {x : V // ∃ y, E x y} where
  toFun xy := ⟨xy.1.1, xy.1.2, xy.2⟩
  invFun x := ⟨(x.val, Classical.choose x.2), Classical.choose_spec x.2⟩
  left_inv xy := Subtype.ext (Prod.ext rfl (hout (Classical.choose_spec
    (show ∃ y, E xy.1.1 y from ⟨xy.1.2, xy.2⟩)) xy.2))
  right_inv _ := rfl

/-- Count the actual relation edges and the extension event under the uniform full-cycle law. -/
theorem edge_and_completion_mass [Finite V] (E : V → V → Prop)
    (hout : Relator.RightUnique E) (hin : Relator.LeftUnique E)
    (hacyclic : ∀ x, ¬ TransGen E x x)
    (hV : 2 ≤ Nat.card V) (hc : 2 ≤ Nat.card (Component E)) :
    Nat.card {xy : V × V // E xy.1 xy.2} = Nat.card V - Nat.card (Component E) ∧
    ∀ (μ : PMF (FullCycle V)),
      (∀ σ, μ σ = (Nat.card (FullCycle V) : ℝ≥0∞)⁻¹) →
      μ.toOuterMeasure {σ | ∀ x y, E x y → σ.1 x = y} =
        ((Nat.card (Component E) - 1).factorial : ℝ≥0∞) /
          ((Nat.card V - 1).factorial : ℝ≥0∞) ∧
      0 < μ.toOuterMeasure {σ | ∀ x y, E x y → σ.1 x = y} := by
  classical
  obtain ⟨q, _, _, _, _, _, hne, hcard, _⟩ :=
    directed_forest_completion E hout hin hacyclic hc
  let := Fintype.ofFinite V
  let := Fintype.ofFinite (Tail E)
  let := Fintype.ofFinite {x : V // ∃ y, E x y}
  constructor
  · rw [Nat.card_congr (edgeSourceEquiv E hout), Nat.card_congr q]
    simp only [Nat.card_eq_fintype_card]
    let p (x : V) := ¬ ∃ y, E x y
    let e : {x : V // ∃ y, E x y} ≃ {x : V // ¬ p x} :=
      Equiv.subtypeEquivProp (funext fun x => propext not_not.symm)
    let := Fintype.ofFinite {x : V // ¬ p x}
    rw [Fintype.card_congr e]
    exact Fintype.card_subtype_compl p
  · intro μ hμ
    let s : Set (FullCycle V) := {σ | ∀ x y, E x y → σ.1 x = y}
    let := Fintype.ofFinite (FullCycle V)
    let := Fintype.ofFinite s
    let : Nonempty (FullCycle V) := hne.map fun σ => ⟨σ.1, σ.2.1⟩
    have hcount : Fintype.card s =
        (Nat.card (Component E) - 1).factorial := by
      rw [← Nat.card_eq_fintype_card]
      exact (Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun σ : Equiv.Perm V => σ.IsCycleOn Set.univ)
        (fun σ => ∀ x y, E x y → σ x = y))).trans hcard
    have hfull : Fintype.card (FullCycle V) = (Nat.card V - 1).factorial := by
      rw [← Nat.card_eq_fintype_card, full_cycle_card hV]
    have hUniform : μ = uniformPmf (FullCycle V) := by
      ext σ
      simpa only [uniformPmf, PMF.ofFintype_apply, Nat.card_eq_fintype_card] using hμ σ
    have hmass : μ.toOuterMeasure s =
        ((Nat.card (Component E) - 1).factorial : ℝ≥0∞) /
          ((Nat.card V - 1).factorial : ℝ≥0∞) := by
      rw [hUniform, uniformPmf_toOuterMeasure_apply, hcount, hfull]
    refine ⟨hmass, ?_⟩
    change 0 < μ.toOuterMeasure s
    rw [hmass, div_eq_mul_inv]
    have hnum : 0 < ((Nat.card (Component E) - 1).factorial : ℝ≥0∞) := by
      exact_mod_cast Nat.factorial_pos (Nat.card (Component E) - 1)
    have hden : ((Nat.card V - 1).factorial : ℝ≥0∞) ≠ ⊤ := by simp
    exact pos_iff_ne_zero.mpr (mul_ne_zero hnum.ne' (ENNReal.inv_pos.mpr hden).ne')

end D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletionCounts
