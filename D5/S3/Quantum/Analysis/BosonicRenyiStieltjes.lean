/- GID: D5/S3/Quantum/Analysis/BosonicRenyiStieltjes
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/BosonicRenyiStieltjes
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positive Stieltjes representation for the bosonic Gaussian Renyi function. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The scalar positive representation used in the Gaussian covariance entropy inequality.
The mass follows from an arctangent primitive after the substitutions
`q = (1 - x) / (1 + x)` and `p = q ^ α`. The logarithmic representation is obtained
by matching derivatives for `ν > 1`, fixing the constant at infinity, and extending to `ν = 1`
using integrability of the logarithmic endpoint singularity. -/

namespace D5.S3.Quantum.Analysis.BosonicRenyiStieltjes

open Real Set MeasureTheory Filter

/-- Single-mode bosonic Gaussian Renyi entropy. -/
def renyiFunction (α ν : ℝ) : ℝ :=
  Real.log (((ν + 1) / 2) ^ α - ((ν - 1) / 2) ^ α) / (α - 1)

/-- Constant in the positive logarithmic representation. -/
def renyiConstant (α : ℝ) : ℝ := Real.log α / (α - 1) - Real.log 2

/-- Density of the positive logarithmic representation on `(0, 1)`. -/
def renyiWeight (α x : ℝ) : ℝ :=
  (-2 * α * Real.sin (Real.pi * α) * (1 - x ^ 2) ^ (α - 1)) /
    (Real.pi * (α - 1) * ((1 + x) ^ (2 * α) + (1 - x) ^ (2 * α) -
      2 * (1 - x ^ 2) ^ α * Real.cos (Real.pi * α)))

private def poissonAngle (α p : ℝ) : ℝ :=
  Real.arctan (p * Real.sin (Real.pi * α) / (1 - p * Real.cos (Real.pi * α)))

private def weightPrimitive (α x : ℝ) : ℝ :=
  poissonAngle α (((1 - x) / (1 + x)) ^ α) / (Real.pi * (α - 1))

private lemma sine_factor_pos {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    0 < -Real.sin (Real.pi * α) / (α - 1) := by
  sorry

private lemma weight_denominator_pos {α x : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 < (1 + x) ^ (2 * α) + (1 - x) ^ (2 * α) -
      2 * (1 - x ^ 2) ^ α * Real.cos (Real.pi * α) := by
  sorry

/-- The Stieltjes density is strictly positive throughout `[0, 1)`. -/
theorem weight_pos {α x : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) : 0 < renyiWeight α x := by
  have hs := sine_factor_pos ha0 ha2 ha1
  have hd := weight_denominator_pos ha0 ha2 ha1 hx0 hx1
  sorry

private lemma mobius_mem {x : ℝ} (hx : x ∈ Ioo 0 1) :
    (1 - x) / (1 + x) ∈ Ioo 0 1 := by
  sorry

private lemma mobius_hasDerivAt {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun y : ℝ => (1 - y) / (1 + y)) (-2 / (1 + x) ^ 2) x := by
  sorry

private lemma power_substitution_hasDerivAt {α x : ℝ} (ha0 : 0 < α)
    (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun y : ℝ => ((1 - y) / (1 + y)) ^ α)
      (-2 * α * ((1 - x) / (1 + x)) ^ (α - 1) / (1 + x) ^ 2) x := by
  have hq := mobius_mem hx
  have hd := mobius_hasDerivAt hx
  sorry

private lemma weight_substitution {α x : ℝ} (ha0 : 0 < α) (hx : x ∈ Ioo 0 1) :
    renyiWeight α x =
      (2 * α * Real.sin (Real.pi * α) * ((1 - x) / (1 + x)) ^ (α - 1)) /
        (Real.pi * (α - 1) * (1 + x) ^ 2 *
          (1 - 2 * ((1 - x) / (1 + x)) ^ α * Real.cos (Real.pi * α) +
            (((1 - x) / (1 + x)) ^ α) ^ 2)) * (-1) := by
  sorry

private lemma poissonAngle_hasDerivAt {α p : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hp : p ∈ Ioo 0 1) :
    HasDerivAt (poissonAngle α)
      (Real.sin (Real.pi * α) /
        (1 - 2 * p * Real.cos (Real.pi * α) + p ^ 2)) p := by
  sorry

private lemma weightPrimitive_continuousOn {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) : ContinuousOn (weightPrimitive α) (Icc 0 1) := by
  sorry

private lemma weightPrimitive_hasDerivAt {α x : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hx : x ∈ Ioo 0 1) :
    HasDerivAt (weightPrimitive α) (renyiWeight α x) x := by
  have hp := power_substitution_hasDerivAt ha0 hx
  have hq := mobius_mem hx
  have hangle := poissonAngle_hasDerivAt ha0 ha2 ha1
  have hw := weight_substitution ha0 hx
  sorry

private lemma weightPrimitive_endpoints {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) : weightPrimitive α 1 - weightPrimitive α 0 = 1 / 2 := by
  sorry

/-- The endpoint singularity of the positive density is integrable. -/
theorem weight_integrable {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    IntegrableOn (renyiWeight α) (Ioo 0 1) := by
  have hc := weightPrimitive_continuousOn ha0 ha2 ha1
  have hd := fun x hx => weightPrimitive_hasDerivAt ha0 ha2 ha1 (x := x) hx
  have hp := fun x (hx : x ∈ Ioo (0 : ℝ) 1) =>
    (weight_pos ha0 ha2 ha1 hx.1.le hx.2).le
  sorry

/-- Every order in the stated range gives a density of mass one half. -/
theorem weight_mass {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x = 1 / 2 := by
  have hi := weight_integrable ha0 ha2 ha1
  have hc := weightPrimitive_continuousOn ha0 ha2 ha1
  have hd := fun x hx => weightPrimitive_hasDerivAt ha0 ha2 ha1 (x := x) hx
  have he := weightPrimitive_endpoints ha0 ha2 ha1
  sorry

private lemma logarithmic_integrable {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 ≤ ν) :
    IntegrableOn (fun x => renyiWeight α x * Real.log (ν ^ 2 - x ^ 2)) (Ioo 0 1) := by
  sorry

private lemma logarithmic_derivative {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    HasDerivAt (fun v => ∫ x in Ioo (0 : ℝ) 1,
      renyiWeight α x * Real.log (v ^ 2 - x ^ 2))
      (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * (2 * ν / (ν ^ 2 - x ^ 2))) ν := by
  sorry

private lemma renyiFunction_hasDerivAt {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    HasDerivAt (renyiFunction α)
      (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * (2 * ν / (ν ^ 2 - x ^ 2))) ν := by
  sorry

private lemma representation_atTop {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) :
    Tendsto (fun ν => renyiFunction α ν -
      ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2))
      atTop (nhds (renyiConstant α)) := by
  have hm := weight_mass ha0 ha2 ha1
  sorry

private lemma representation_of_one_lt {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 < ν) :
    renyiFunction α ν = renyiConstant α +
      ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2) := by
  have hd := logarithmic_derivative ha0 ha2 ha1
  have hs := renyiFunction_hasDerivAt ha0 ha2 ha1
  have ht := representation_atTop ha0 ha2 ha1
  sorry

private lemma representation_at_one {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) :
    renyiFunction α 1 = renyiConstant α +
      ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (1 ^ 2 - x ^ 2) := by
  have hr := representation_of_one_lt ha0 ha2 ha1
  have hi := logarithmic_integrable ha0 ha2 ha1 (ν := 1) le_rfl
  sorry

/-- Positive logarithmic Stieltjes representation, including the pure-mode endpoint. -/
theorem stieltjes_representation {α ν : ℝ} (ha0 : 0 < α) (ha2 : α < 2)
    (ha1 : α ≠ 1) (hv : 1 ≤ ν) :
    IntegrableOn (fun x => renyiWeight α x * Real.log (ν ^ 2 - x ^ 2)) (Ioo 0 1) ∧
      renyiFunction α ν = renyiConstant α +
        ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2) := by
  refine ⟨logarithmic_integrable ha0 ha2 ha1 hv, ?_⟩
  rcases eq_or_lt_of_le hv with hv | hv
  · subst ν
    exact representation_at_one ha0 ha2 ha1
  · exact representation_of_one_lt ha0 ha2 ha1 hv

/-- The scalar input to the Gaussian covariance entropy settlement. -/
theorem result {α : ℝ} (ha0 : 0 < α) (ha2 : α < 2) (ha1 : α ≠ 1) :
    (∀ x ∈ Ico (0 : ℝ) 1, 0 < renyiWeight α x) ∧
      IntegrableOn (renyiWeight α) (Ioo 0 1) ∧
      (∫ x in Ioo (0 : ℝ) 1, renyiWeight α x) = 1 / 2 ∧
      ∀ ν, 1 ≤ ν →
        IntegrableOn (fun x => renyiWeight α x * Real.log (ν ^ 2 - x ^ 2)) (Ioo 0 1) ∧
          renyiFunction α ν = renyiConstant α +
            ∫ x in Ioo (0 : ℝ) 1, renyiWeight α x * Real.log (ν ^ 2 - x ^ 2) := by
  exact ⟨fun x hx => weight_pos ha0 ha2 ha1 hx.1 hx.2,
    weight_integrable ha0 ha2 ha1, weight_mass ha0 ha2 ha1,
    fun ν hv => stieltjes_representation ha0 ha2 ha1 hv⟩

end D5.S3.Quantum.Analysis.BosonicRenyiStieltjes
