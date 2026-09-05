/- GID: D5/S1/Depth/HeightScaleNormalizationSeparation
   generality: I
   mirror-B: D5/B/S1/Depth/HeightScaleNormalizationSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Polynomial denominator depth and golden continued-fraction depth admit separate but no common positive normalization. -/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/- Library-search audit trail (2026-09-05):
   * Repository searches found the golden continued-fraction and effective
     Hurwitz modules, but no theorem excluding a common normalization of the
     denominator and continued-fraction depth scales.
   * Pinned Mathlib supplies
     `tendsto_pow_const_mul_const_pow_of_lt_one` and limit uniqueness, but no
     combined theorem quantifying over an arbitrary normalizing weight.
   * The private normalization-transfer lemma is the escape witness: it uses
     polynomial-versus-geometric decay on the active path to the public
     common-normalizer obstruction. -/

namespace D5.S1.Depth.HeightScaleNormalizationSeparation

open Filter

/-- The inverse-square error scale at positive denominator level `Q + 1`. -/
noncomputable def denominatorErrorScale (Q : Nat) : Real :=
  1 / (((Q + 1 : Nat) : Real) ^ 2)

/-- The inverse-golden-square error scale at positive continued-fraction depth `Q + 1`. -/
noncomputable def continuedFractionErrorScale (Q : Nat) : Real :=
  (Real.goldenRatio⁻¹ ^ 2) ^ (Q + 1)

private theorem golden_inverse_square_nonneg :
    0 <= Real.goldenRatio⁻¹ ^ 2 := by
  positivity

private theorem golden_inverse_square_lt_one :
    Real.goldenRatio⁻¹ ^ 2 < 1 := by
  exact pow_lt_one₀ (inv_nonneg.mpr Real.goldenRatio_pos.le)
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio) (by norm_num)

private theorem scale_ratio_tendsto_zero :
    Tendsto
      (fun Q : Nat => continuedFractionErrorScale Q / denominatorErrorScale Q)
      atTop (nhds 0) := by
  have h :=
    (tendsto_pow_const_mul_const_pow_of_lt_one 2
      golden_inverse_square_nonneg golden_inverse_square_lt_one).comp
      (tendsto_add_atTop_nat 1)
  refine h.congr (fun Q => ?_)
  simp only [Function.comp_apply, denominatorErrorScale, continuedFractionErrorScale]
  have hQ : (((Q + 1 : Nat) : Real) : Real) ≠ 0 := by positivity
  field_simp

/-- Once a weight normalizes inverse-square denominator error to a finite
limit, the same weight sends the exponentially smaller depth error to zero. -/
private theorem continued_fraction_normalization_vanishes
    (weight : Nat -> Real) (limit : Real)
    (hDenominator : Tendsto
      (fun Q => weight Q * denominatorErrorScale Q) atTop (nhds limit)) :
    Tendsto
      (fun Q => weight Q * continuedFractionErrorScale Q) atTop (nhds 0) := by
  have hProduct := hDenominator.mul scale_ratio_tendsto_zero
  have hLimit : limit * 0 = (0 : Real) := by ring
  rw [hLimit] at hProduct
  refine hProduct.congr (fun Q => ?_)
  have hScale : denominatorErrorScale Q ≠ 0 := by
    unfold denominatorErrorScale
    positivity
  field_simp [hScale]

/-- Each of the denominator and continued-fraction depth scales has its own
exact normalizer, but no single weight can normalize both to finite positive
limits.  This is the precise asymptotic sense in which the approximation scale
class depends on the chosen height. -/
theorem height_scale_normalization_separation :
    (∃ weight : Nat -> Real,
      Tendsto (fun Q => weight Q * denominatorErrorScale Q) atTop (nhds 1)) ∧
    (∃ weight : Nat -> Real,
      Tendsto (fun Q => weight Q * continuedFractionErrorScale Q) atTop (nhds 1)) ∧
    ∀ (weight : Nat -> Real) (denominatorLimit depthLimit : Real),
      0 < denominatorLimit -> 0 < depthLimit ->
      ¬(Tendsto (fun Q => weight Q * denominatorErrorScale Q)
          atTop (nhds denominatorLimit) ∧
        Tendsto (fun Q => weight Q * continuedFractionErrorScale Q)
          atTop (nhds depthLimit)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun Q => (((Q + 1 : Nat) : Real) ^ 2), ?_⟩
    have hPointwise :
        (fun Q : Nat => (((Q + 1 : Nat) : Real) ^ 2) * denominatorErrorScale Q) =
          fun _ => (1 : Real) := by
      funext Q
      have hQ : (((Q + 1 : Nat) : Real) : Real) ≠ 0 := by positivity
      simp only [denominatorErrorScale]
      field_simp
    rw [hPointwise]
    exact tendsto_const_nhds
  · refine ⟨fun Q => (continuedFractionErrorScale Q)⁻¹, ?_⟩
    have hPointwise :
        (fun Q : Nat => (continuedFractionErrorScale Q)⁻¹ *
          continuedFractionErrorScale Q) = fun _ => (1 : Real) := by
      funext Q
      exact inv_mul_cancel₀
        (pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero Real.goldenRatio_ne_zero)))
    rw [hPointwise]
    exact tendsto_const_nhds
  · intro weight denominatorLimit depthLimit hDenominatorPositive hDepthPositive hBoth
    have hZero := continued_fraction_normalization_vanishes
      weight denominatorLimit hBoth.1
    have hDepthZero : depthLimit = 0 := tendsto_nhds_unique hBoth.2 hZero
    linarith

#print axioms height_scale_normalization_separation

end D5.S1.Depth.HeightScaleNormalizationSeparation
