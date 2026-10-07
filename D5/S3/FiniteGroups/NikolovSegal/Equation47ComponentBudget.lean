/- GID: D5/S3/FiniteGroups/NikolovSegal/Equation47ComponentBudget
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Equation47ComponentBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-group coordinate, extraction or product mathematics. -/

import D5.S3.FiniteGroups.NikolovSegal.Equation47ValueSequence
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-! Part I p222 and pp225,230, localized to the actual powered components.
Moved coordinates are bounded by twice the genuine nonbase VALUE count.
This supplies the final residual support budget after the component's links.
-/
namespace NikolovSegal.Equation47ValueNormalization
open Equation47 Equation47TypeII Equation47WordCoupling Equation47Colours List
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {m : ℕ}

private theorem base_apply (sigma : Equiv.Perm I) (v : I) :
    base sigma (sigma v) = base sigma v := by
  apply congrArg Quotient.out
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl sigma v).apply_left

private theorem moved_le_nonbase (sigma : Equiv.Perm I) (A : Finset I)
    (hA : ∀ v ∈ A, sigma v ∈ A) :
    (A.filter (fun v => sigma v ≠ v)).card ≤
      2 * (A.filter (fun v => v ≠ base sigma v)).card := by
  classical
  let B := A.filter (fun v => v ≠ base sigma v)
  let C := A.filter (fun v => sigma v ≠ v ∧ v = base sigma v)
  have hC : C.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn sigma
    · intro v hv
      obtain ⟨hvA,hm,hb⟩ := Finset.mem_filter.mp hv
      apply Finset.mem_filter.mpr
      refine ⟨hA v hvA,?_⟩
      rw [base_apply,← hb]
      exact hm
    · exact sigma.injective.injOn
  have hM : A.filter (fun v => sigma v ≠ v) ⊆ B ∪ C := by
    intro v hv
    obtain ⟨hvA,hm⟩ := Finset.mem_filter.mp hv
    by_cases hb : v = base sigma v
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvA,hm,hb⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvA,hb⟩)
  have hh := (Finset.card_le_card hM).trans (Finset.card_union_le B C)
  change _ ≤ 2*B.card
  omega

private theorem component_invariant (tau : Fin m → Equiv.Perm I) (r : I → I)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (root : I) (j : Fin m) :
    ∀ v ∈ Finset.univ.filter (fun v : I => r v = root),
      tau j v ∈ Finset.univ.filter (fun v : I => r v = root) := by
  intro v hv
  have hr := (Finset.mem_filter.mp hv).2
  have he : r v = r (tau j v) := by
    by_cases h : v = tau j v
    · exact congrArg r h
    · exact hconst v (tau j v) (show (qPowerGraph tau 1).Reachable v (tau j v) from
        (show (qPowerGraph tau 1).Adj v (tau j v) from
          ⟨h,j,Or.inl (by simp)⟩).reachable)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.symm.trans hr⟩

/-- The genuine movement sum on ONE true component is controlled by its
actual free VALUE variables.  No full-block coverage or scalar hypothesis
is involved, and the component can be disconnected from every other root. -/
theorem component_movement_value_bound (tau : Fin m → Equiv.Perm I) (r : I → I)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w) (root : I) :
    (∑ j : Fin m, (Finset.univ.filter (fun v : I =>
      r v = root ∧ tau j v ≠ v)).card) ≤
      2 * (Finset.univ.filter (fun e : Arc m I =>
        e.2 ≠ base (tau e.1) e.2 ∧ r e.2 = root)).card := by
  classical
  let A := Finset.univ.filter (fun v : I => r v = root)
  let B := Finset.univ.filter (fun e : Arc m I =>
    e.2 ≠ base (tau e.1) e.2 ∧ r e.2 = root)
  have hcount : B.card = ∑ j : Fin m, (A.filter (fun v => v ≠ base (tau j) v)).card := by
    change (Finset.univ.filter (fun e : Fin m × I =>
      e.2 ≠ base (tau e.1) e.2 ∧ r e.2 = root)).card = _
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter,A]
    rw [← Finset.univ_product_univ,Finset.sum_product]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : r v = root <;> by_cases hb : v ≠ base (tau j) v <;>
      simp only [h,hb,true_and,false_and,and_true,and_false,ite_true,ite_false]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
    moved_le_nonbase (tau j) A (component_invariant tau r hconst root j))
  rw [← Finset.mul_sum,← hcount] at hh
  simpa only [A,Finset.filter_filter] using hh

/-- The final actual component residual meets Proposition8.4's support
threshold under the paper's component movement condition.  Its own n-1
links and its own cardinal n are counted; original transitivity is unused. -/
theorem normalized_component_typeII_residual_budget {D : ℕ}
    (tau : Fin m → Equiv.Perm I) (L : List (I × Arc m I)) (hL : ValueLeafOrder tau L)
    (r : I → I) (hroots : ∀ v, (∃ p ∈ L, p.1 = v) ↔ v ≠ r v)
    (hconst : ∀ v w, (qPowerGraph tau 1).Reachable v w → r v = r w)
    (root : I) (hroot : root = r root)
    (hn : 2 ≤ (Finset.univ.filter (fun v : I => r v = root)).card)
    (htype : (4+2*D) * (Finset.univ.filter (fun v : I => r v = root)).card ≤
      ∑ j : Fin m, (Finset.univ.filter (fun v : I => r v = root ∧ tau j v ≠ v)).card) :
    (Finset.univ.filter (fun v : I => r v = root)).card + 2*D + 1 ≤
      (valueResidualSupport tau L r root).card := by
  have hm := component_movement_value_bound tau r hconst root
  have hc := normalized_component_residual_pair_count tau L hL r hroots hconst root hroot
  have hsub : (Finset.univ.filter (fun v : I => r v = root)).card - 1 + 1 =
      (Finset.univ.filter (fun v : I => r v = root)).card := by omega
  nlinarith

end NikolovSegal.Equation47ValueNormalization
