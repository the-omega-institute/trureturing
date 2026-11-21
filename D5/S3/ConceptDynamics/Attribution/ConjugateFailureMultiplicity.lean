/- GID: D5/S3/ConceptDynamics/Attribution/ConjugateFailureMultiplicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/ConjugateFailureMultiplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Multiplicities of conjugate failure events bound fixed mass under normal closure. -/

import D5.S3.ConceptDynamics.Attribution.FixedKernelMass
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

open Finset
open D5.S3.ConceptDynamics.Attribution.FixedKernelMass

namespace D5.S3.ConceptDynamics.Attribution.ConjugateFailureMultiplicity

variable {G S : Type*} [Group G] [MulAction G S] [Fintype S]

/-- If every seed moved by the normal closure lies in at least d conjugate failure events,
then each unit of normal-closure loss contributes at least d units to the incidence sum. -/
theorem normal_closure_loss_mul_le (H : Subgroup G) (a : S → ℝ)
    (nonneg : ∀ s, 0 ≤ a s) (invariant : ∀ (g : G) s, a (g • s) = a s) (d : ℕ) :
    let lossSets := Set.range fun g : G => {s : S | ¬∀ h : H, h • (g⁻¹ • s) = g⁻¹ • s}
    let N := Subgroup.normalClosure (H : Set G)
    let total := ∑ s, a s
    (∀ s : S, 0 < a s → (¬∀ n : N, n • s = s) →
      d ≤ Nat.card {B : lossSets // s ∈ B.val}) →
      (d : ℝ) * (total - seedFixedMass (G := N) a) ≤
        (Nat.card ↥lossSets : ℝ) * (total - seedFixedMass (G := H) a) := by
  classical
  let N := Subgroup.normalClosure (H : Set G)
  let broken (g : G) : Set S := {s | ¬∀ h : H, h • (g⁻¹ • s) = g⁻¹ • s}
  let Events := Set.range broken
  let _ : Fintype Events := Fintype.ofFinite _
  let normalFixed (s : S) := ∀ n : N, n • s = s
  let lost (B : Events) (s : S) : ℝ := if s ∈ B.val then a s else 0
  let lostNormal (s : S) : ℝ := if normalFixed s then 0 else a s
  intro _ _ _ multiplicity
  have lost_nonneg (B : Events) (s : S) : 0 ≤ lost B s := by
    unfold lost
    split <;> [exact nonneg s; exact le_rfl]
  have pointwise (s : S) : (d : ℝ) * lostNormal s ≤ ∑ B, lost B s := by
    unfold lostNormal
    split
    · simp only [mul_zero]
      exact sum_nonneg (fun B _ => lost_nonneg B s)
    · next hf =>
      by_cases hz : a s = 0
      · rw [hz, mul_zero]
        exact sum_nonneg (fun B _ => lost_nonneg B s)
      · have lower := multiplicity s (lt_of_le_of_ne (nonneg s) (Ne.symm hz)) hf
        let f : Finset Events := univ.filter fun B => s ∈ B.val
        have card : f.card = Nat.card {B : Events // s ∈ B.val} := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        calc
          (d : ℝ) * a s ≤ (f.card : ℝ) * a s := by
            rw [card]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast lower) (nonneg s)
          _ = ∑ B, lost B s := by
            rw [show (fun B => lost B s) = (fun B => if s ∈ B.val then a s else 0) by rfl,
              ← sum_filter, sum_const, nsmul_eq_mul]
  have complement (p : S → Prop) [DecidablePred p] :
      (∑ s, if p s then 0 else a s) = ∑ s, a s - ∑ s, (if p s then a s else 0) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun s _ => by split <;> simp_all)
  have equal_loss (B : Events) :
      (∑ s, lost B s) = ∑ s, a s - seedFixedMass (G := H) a := by
    obtain ⟨g, eq⟩ := B.property
    let move : Equiv.Perm S := MulAction.toPerm g
    rw [← Equiv.sum_comp move]
    have summands : (fun s => lost B (move s)) =
        fun s => if ∀ h : H, h • s = s then 0 else a s := by
      funext s
      unfold lost
      rw [← eq]
      simp only [broken, Set.mem_ofPred_eq, move, MulAction.toPerm_apply, inv_smul_smul,
        ite_not, invariant]
    rw [summands, complement, seedFixedMass, sum_filter]
  have normal_loss : (∑ s, lostNormal s) =
      ∑ s, a s - seedFixedMass (G := N) a := by
    rw [seedFixedMass, sum_filter]
    exact complement normalFixed
  have all : (d : ℝ) * (∑ s, lostNormal s) ≤
      (Fintype.card Events : ℝ) * (∑ s, a s - seedFixedMass (G := H) a) := calc
    _ = ∑ s : S, (d : ℝ) * lostNormal s := mul_sum _ _ _
    _ ≤ ∑ s : S, ∑ B : Events, lost B s := sum_le_sum (fun s _ => pointwise s)
    _ = _ := by rw [sum_comm]; simp only [equal_loss, sum_const, card_univ, nsmul_eq_mul]
  rw [normal_loss] at all
  rw [Nat.card_eq_fintype_card]
  exact all

end D5.S3.ConceptDynamics.Attribution.ConjugateFailureMultiplicity
