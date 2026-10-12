/- GID: D5/S3/ConceptDynamics/Coding/ResetQuadraticGaussianCokernel
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetQuadraticGaussianCokernel
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Exact integral rank-two cokernel of the reset two-step defect at q=3 modulo four. -/
import D5.S1.Recurrence.QuadraticCompanionDefect
import D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ResetQuadraticGaussianCokernel
open Multiplicative
open scoped BigOperators
open D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
  (VertexModule transition DimensionGroup)
open D5.S1.Recurrence.QuadraticCompanionDefect
open private flip_twice from D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
open private flip_coeff sign_cases from D5.S3.ConceptDynamics.Coding.ResetFiniteIntegralDefect

private abbrev RingRow := MonoidAlgebra ℤ Sign
private abbrev tau : Sign := ofAdd true

/-- Identity plus the square of the original integer right-row transition. -/
def resetTwoStepDefect (q : ℕ) : Module.End ℤ (VertexModule Sign q) :=
  LinearMap.id + transition (resetMatrix q) ^ 2

private def difference : RingRow →+ ℤ where
  toFun x := x.coeff 1 - x.coeff tau
  map_zero' := by simp
  map_add' x y := by
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply]; ring

private theorem difference_sum_flip (x : RingRow) : difference (x + resetFlip x) = 0 := by
  have ht : tau * tau = (1 : Sign) := by decide
  simp only [difference, AddMonoidHom.coe_mk, ZeroHom.coe_mk, MonoidAlgebra.coeff_add,
    Finsupp.add_apply, flip_coeff, one_mul, ht]
  ring

private theorem sum_flip_image (y : RingRow) :
    (∃ x : RingRow, x + resetFlip x = y) ↔ difference y = 0 := by
  constructor
  · rintro ⟨x, rfl⟩; exact difference_sum_flip x
  · intro hy
    have hh : y.coeff 1 = y.coeff tau := sub_eq_zero.mp hy
    refine ⟨MonoidAlgebra.single 1 (y.coeff 1), ?_⟩
    ext h
    have ht : tau * tau = (1 : Sign) := by decide
    have hn : tau ≠ (1 : Sign) := by decide
    rcases sign_cases h with rfl | rfl <;>
      simp [MonoidAlgebra.coeff_add, flip_coeff, MonoidAlgebra.coeff_single, hh,
        ht, hn, Ne.symm hn]

private theorem transition_sum (n : ℕ) (v : VertexModule Sign (n + 2)) :
    (∑ i, transition (resetMatrix (n + 2)) v i) =
      resetFlip (∑ i, v i) + prefixSum n v := by
  rw [Fin.sum_univ_succ, transition_zero]
  simp only [transition_succ]
  rfl

private theorem two_step_companion (n : ℕ) (v : VertexModule Sign (n + 2)) :
    resetTwoStepDefect (n + 2) v = companion resetFlip n v := by
  funext j
  change (v + ((transition (resetMatrix (n + 2))) ^ 2) v) j = _
  rw [pow_two, Module.End.mul_apply]
  refine Fin.cases ?_ (fun k => ?_) j
  · change v 0 + transition (resetMatrix (n + 2))
        (transition (resetMatrix (n + 2)) v) 0 = _
    rw [transition_zero, transition_sum]
    rfl
  · refine Fin.cases ?_ (fun l => ?_) k
    · change v (0 : Fin (n + 1)).succ + transition (resetMatrix (n + 2))
        (transition (resetMatrix (n + 2)) v) (0 : Fin (n + 1)).succ = _
      rw [transition_succ, Fin.castSucc_zero, transition_zero]
      rfl
    · change v l.succ.succ + transition (resetMatrix (n + 2))
        (transition (resetMatrix (n + 2)) v) l.succ.succ = _
      rw [transition_succ, Fin.castSucc_succ, transition_succ]
      rfl

private theorem residual_eliminate (m : ℕ) (v : VertexModule Sign (4 * m + 3)) :
    codomainEquiv resetFlip (4 * m + 1) (resetTwoStepDefect (4 * m + 3) v) =
      ((v 0 + v (0 : Fin (4 * m + 2)).succ +
          resetFlip (v 0 + v (0 : Fin (4 * m + 2)).succ),
        v (0 : Fin (4 * m + 2)).succ + resetFlip (v (0 : Fin (4 * m + 2)).succ)),
        (domainEquiv (4 * m + 1) v).2) := by
  rw [two_step_companion, eliminate, boundary_three_mod_four resetFlip flip_twice]

/-- Two primitive integral obstructions read the independent residual heads.
They retain both original sign coefficients and all original suffix coordinates. -/
def resetGaussianCharacter (m : ℕ) : VertexModule Sign (4 * m + 3) →ₗ[ℤ] ℤ × ℤ :=
  ({
      toFun := fun y =>
        let z := codomainEquiv resetFlip (4 * m + 1) y
        (difference z.1.1, difference z.1.2)
      map_zero' := by simp
      map_add' := by
        intro y w
        simp only [map_add]
        change (difference ((codomainEquiv resetFlip (4 * m + 1) y).1.1 +
            (codomainEquiv resetFlip (4 * m + 1) w).1.1),
          difference ((codomainEquiv resetFlip (4 * m + 1) y).1.2 +
            (codomainEquiv resetFlip (4 * m + 1) w).1.2)) = _
        rw [map_add, map_add]
        rfl
    } : VertexModule Sign (4 * m + 3) →+ ℤ × ℤ).toIntLinearMap

private theorem character_surjective (m : ℕ) :
    Function.Surjective (resetGaussianCharacter m) := by
  intro z
  refine ⟨(codomainEquiv resetFlip (4 * m + 1)).symm
      ((MonoidAlgebra.single 1 z.1, MonoidAlgebra.single 1 z.2), 0), ?_⟩
  change (difference ((codomainEquiv resetFlip (4 * m + 1)
      ((codomainEquiv resetFlip (4 * m + 1)).symm _)).1.1),
    difference ((codomainEquiv resetFlip (4 * m + 1)
      ((codomainEquiv resetFlip (4 * m + 1)).symm _)).1.2)) = z
  rw [AddEquiv.apply_symm_apply]
  have hn : tau ≠ (1 : Sign) := by decide
  simp [difference, MonoidAlgebra.coeff_single, hn, Ne.symm hn]

/-- At every q=4m+3, these two integer equations are exactly solvability of
the genuine two-step defect on the full two-coefficient integer lattice. -/
theorem reset_two_step_three_mod_four_image (m : ℕ)
    (y : VertexModule Sign (4 * m + 3)) :
    (∃ v, resetTwoStepDefect (4 * m + 3) v = y) ↔ resetGaussianCharacter m y = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    change (difference ((codomainEquiv resetFlip (4 * m + 1)
        (resetTwoStepDefect (4 * m + 3) v)).1.1),
      difference ((codomainEquiv resetFlip (4 * m + 1)
        (resetTwoStepDefect (4 * m + 3) v)).1.2)) = 0
    rw [residual_eliminate]
    rw [difference_sum_flip, difference_sum_flip]
    rfl
  · intro hy
    let z := codomainEquiv resetFlip (4 * m + 1) y
    have hz : (difference z.1.1, difference z.1.2) = (0, 0) := hy
    obtain ⟨a, ha⟩ := (sum_flip_image z.1.1).mpr (congrArg Prod.fst hz)
    obtain ⟨b, hb⟩ := (sum_flip_image z.1.2).mpr (congrArg Prod.snd hz)
    let v := (domainEquiv (4 * m + 1)).symm ((a - b, b), z.2)
    refine ⟨v, (codomainEquiv resetFlip (4 * m + 1)).injective ?_⟩
    have hd : domainEquiv (4 * m + 1) v = ((a - b, b), z.2) :=
      AddEquiv.apply_symm_apply _ _
    have hhead : v 0 = a - b := congrArg (fun u => u.1.1) hd
    have hsecond : v (0 : Fin (4 * m + 2)).succ = b := congrArg (fun u => u.1.2) hd
    have htail : (domainEquiv (4 * m + 1) v).2 = z.2 := by
      simpa only using congrArg (fun u : (RingRow × RingRow) × (Fin (4 * m + 1) → RingRow) =>
        u.2) hd
    rw [residual_eliminate, hhead, hsecond, htail, sub_add_cancel, ha, hb]

private theorem reset_two_step_range (m : ℕ) :
    LinearMap.range (resetTwoStepDefect (4 * m + 3)) =
      LinearMap.ker (resetGaussianCharacter m) := by
  ext y
  exact reset_two_step_three_mod_four_image m y

/-- The exact ordinary integral cokernel is free of rank two. The character
gives a primitive quotient, so no hidden order-two torsion remains. -/
def resetGaussianCokernelEquiv (m : ℕ) :
    (VertexModule Sign (4 * m + 3) ⧸ LinearMap.range (resetTwoStepDefect (4 * m + 3)))
      ≃ₗ[ℤ] ℤ × ℤ :=
  (Submodule.quotEquivOfEq _ _ (reset_two_step_range m)).trans
    ((resetGaussianCharacter m).quotKerEquivOfSurjective (character_surjective m))

end D5.S3.ConceptDynamics.Coding.ResetQuadraticGaussianCokernel
