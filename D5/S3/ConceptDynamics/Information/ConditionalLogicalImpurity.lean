/- GID: D5/S3/ConceptDynamics/Information/ConditionalLogicalImpurity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Information/ConditionalLogicalImpurity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zero conditional pair impurity characterizes fiberwise target constancy. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/- Library-search audit trail (2026-08-22):
   * Repository searches found no existing conditional logical impurity primitive
     or zero-impurity characterization.
   * The exact family hit `ConceptFiberDecomposition.Concept` supplies the
     canonical readout carrier and is imported directly.
   * Pinned Mathlib exact hits `ENNReal.tsum_eq_zero`,
     `ENNReal.div_eq_zero_iff`, and `PMF.tsum_coe_indicator_ne_top` reduce the
     statement to pointwise vanishing of nonnegative pair-disagreement mass. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Information.ConditionalLogicalImpurity

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- The probability mass of one concept fiber. -/
noncomputable def conceptFiberMass {X B : Type*}
    (mu : PMF X) (concept : Concept X B) (b : B) : ENNReal := by
  classical
  exact ∑' x, {x | concept x = b}.indicator mu x

/-- The mass of ordered pairs in one concept fiber on which the target differs. -/
noncomputable def pairDisagreementMass {X B A : Type*}
    (mu : PMF X) (concept : Concept X B) (target : Concept X A) (b : B) : ENNReal := by
  classical
  exact ∑' x, ∑' y,
      if concept x = b ∧ concept y = b ∧ target x ≠ target y then
        mu x * mu y
      else 0

/-- Conditional logical impurity is the total fiber-normalized pair-disagreement mass. -/
noncomputable def conditionalLogicalImpurity {X B A : Type*}
    (mu : PMF X) (concept : Concept X B) (target : Concept X A) : ENNReal :=
  ∑' b, pairDisagreementMass mu concept target b /
    conceptFiberMass mu concept b

private theorem conceptFiberMass_ne_top {X B : Type*}
    (mu : PMF X) (concept : Concept X B) (b : B) :
    conceptFiberMass mu concept b ≠ ⊤ := by
  exact mu.tsum_coe_indicator_ne_top {x | concept x = b}

private theorem conceptFiberMass_eq_zero_iff {X B : Type*}
    (mu : PMF X) (concept : Concept X B) (b : B) :
    conceptFiberMass mu concept b = 0 ↔
      ∀ x, concept x = b → mu x = 0 := by
  classical
  rw [conceptFiberMass, ENNReal.tsum_eq_zero]
  constructor
  · intro h x hx
    simpa [Set.indicator, hx] using h x
  · intro h x
    by_cases hx : concept x = b
    · simpa [Set.indicator, hx] using h x hx
    · simp [Set.indicator, hx]

private theorem pairDisagreementMass_eq_zero_of_fiber_constant
    {X B A : Type*} (mu : PMF X) (concept : Concept X B)
    (target : Concept X A) (b : B) (t : A)
    (hconstant : ∀ x, concept x = b → mu x ≠ 0 → target x = t) :
    pairDisagreementMass mu concept target b = 0 := by
  classical
  rw [pairDisagreementMass, ENNReal.tsum_eq_zero]
  intro x
  rw [ENNReal.tsum_eq_zero]
  intro y
  by_cases hx : concept x = b
  · by_cases hy : concept y = b
    · by_cases hmuX : mu x = 0
      · simp [hx, hy, hmuX]
      · by_cases hmuY : mu y = 0
        · simp [hx, hy, hmuY]
        · have htarget : target x = target y :=
            (hconstant x hx hmuX).trans (hconstant y hy hmuY).symm
          simp [hx, hy, htarget]
    · simp [hy]
  · simp [hx]

/-- Conditional logical impurity vanishes exactly when the target is constant
on the probability support inside every positive-mass concept fiber. -/
theorem zero_impurity_iff_fiber_ae_constant
    {X B A : Type*} (mu : PMF X) (concept : Concept X B)
    (target : Concept X A) :
    conditionalLogicalImpurity mu concept target = 0 ↔
      ∀ b, conceptFiberMass mu concept b ≠ 0 →
        ∃ t, ∀ x, concept x = b → mu x ≠ 0 → target x = t := by
  classical
  constructor
  · intro himpurity b hb
    have hquotient : pairDisagreementMass mu concept target b /
        conceptFiberMass mu concept b = 0 :=
      ENNReal.tsum_eq_zero.mp himpurity b
    have hpairs : pairDisagreementMass mu concept target b = 0 :=
      (ENNReal.div_eq_zero_iff.mp hquotient).resolve_right
        (conceptFiberMass_ne_top mu concept b)
    have hexists : ∃ x, concept x = b ∧ mu x ≠ 0 := by
      by_contra hnone
      push Not at hnone
      exact hb ((conceptFiberMass_eq_zero_iff mu concept b).2 hnone)
    obtain ⟨x₀, hx₀, hmu₀⟩ := hexists
    refine ⟨target x₀, ?_⟩
    intro x hx hmu
    have hxsum := ENNReal.tsum_eq_zero.mp
      (ENNReal.tsum_eq_zero.mp hpairs x₀) x
    by_contra htarget
    have htarget' : target x₀ ≠ target x := Ne.symm htarget
    have hproduct : mu x₀ * mu x = 0 := by
      rw [if_pos ⟨hx₀, hx, htarget'⟩] at hxsum
      exact hxsum
    exact (mul_ne_zero hmu₀ hmu) hproduct
  · intro hconstant
    rw [conditionalLogicalImpurity, ENNReal.tsum_eq_zero]
    intro b
    by_cases hb : conceptFiberMass mu concept b = 0
    · have hzero : ∀ x, concept x = b → mu x = 0 :=
        (conceptFiberMass_eq_zero_iff mu concept b).1 hb
      have hpairs : pairDisagreementMass mu concept target b = 0 :=
        pairDisagreementMass_eq_zero_of_fiber_constant mu concept target b
          (target mu.support_nonempty.some)
          (fun x hx hmu => (hmu (hzero x hx)).elim)
      simp only [hpairs, ENNReal.zero_div]
    · obtain ⟨t, ht⟩ := hconstant b hb
      have hpairs : pairDisagreementMass mu concept target b = 0 :=
        pairDisagreementMass_eq_zero_of_fiber_constant mu concept target b t ht
      simp only [hpairs, ENNReal.zero_div]

/-- On a two-point distribution, a constant target has zero conditional impurity. -/
example :
    conditionalLogicalImpurity (PMF.pure true)
      (fun _ : Bool => ()) (fun _ : Bool => false) = 0 := by
  apply (zero_impurity_iff_fiber_ae_constant
    (PMF.pure true) (fun _ : Bool => ()) (fun _ : Bool => false)).2
  intro b _
  exact ⟨false, fun _ _ _ => rfl⟩

/-- A full-support two-point law with a varying target does not have zero impurity. -/
example :
    let mu : PMF Bool := PMF.ofFintype (fun _ => (2 : ENNReal)⁻¹) (by
      rw [Fintype.sum_bool, ← two_mul]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))
    conditionalLogicalImpurity mu (fun _ : Bool => ()) id ≠ 0 := by
  dsimp only
  let mu : PMF Bool := PMF.ofFintype (fun _ => (2 : ENNReal)⁻¹) (by
    rw [Fintype.sum_bool, ← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))
  intro himpurity
  have hconstant := (zero_impurity_iff_fiber_ae_constant
    mu (fun _ : Bool => ()) id).1 himpurity
  have hmass : conceptFiberMass mu (fun _ : Bool => ()) () ≠ 0 := by
    intro hzero
    have hpoint := (conceptFiberMass_eq_zero_iff
      mu (fun _ : Bool => ()) ()).1 hzero true rfl
    simp [mu] at hpoint
  obtain ⟨t, ht⟩ := hconstant () hmass
  have hfalse := ht false rfl (by simp [mu])
  have htrue := ht true rfl (by simp [mu])
  exact Bool.noConfusion (hfalse.trans htrue.symm)

#print axioms zero_impurity_iff_fiber_ae_constant

end D5.S3.ConceptDynamics.Information.ConditionalLogicalImpurity
