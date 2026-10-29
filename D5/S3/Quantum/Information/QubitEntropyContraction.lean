/- GID: D5/S3/Quantum/Information/QubitEntropyContraction
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/QubitEntropyContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic contraction of actual equal-spectrum qubit Holevo entropy. -/

import D5.S3.Quantum.Entanglement.GraphDensity.FormationBounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Information.QubitEntropyContraction
open Set Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Information.PartialTraceMutualInformation

private def radialEntropy (u : ℝ) : ℝ := Real.binEntropy ((1 + Real.sqrt u) / 2)
private def logRatio (r : ℝ) : ℝ := Real.log (1 + r) - Real.log (1 - r)

private lemma logRatio_deriv {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt logRatio (2 / (1 - r ^ 2)) r := by
  have hp : 1 + r ≠ 0 := by linarith [hr.1]
  have hm : 1 - r ≠ 0 := by linarith [hr.2]
  have hd : 1 - r ^ 2 ≠ 0 := by nlinarith [hr.1, hr.2]
  have h := (((hasDerivAt_id r).const_add 1).log hp).sub
    (((hasDerivAt_const r 1).sub (hasDerivAt_id r)).log hm)
  convert h using 1 <;> dsimp [logRatio]
  field_simp
  ring

private lemma logRatio_bound {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    logRatio r ≤ 2 * r / (1 - r ^ 2) := by
  let g := fun r : ℝ => 2 * r / (1 - r ^ 2) - logRatio r
  have hg (r : ℝ) (hr : r ∈ Ico (0 : ℝ) 1) :
      HasDerivAt g (4 * r ^ 2 / (1 - r ^ 2) ^ 2) r := by
    have hd : 1 - r ^ 2 ≠ 0 := by nlinarith [hr.1, hr.2]
    have h := (((hasDerivAt_id r).const_mul 2).div
      ((hasDerivAt_const r 1).sub ((hasDerivAt_id r).pow 2)) hd).sub
      (logRatio_deriv ⟨by linarith [hr.1], hr.2⟩)
    convert h using 1 <;> dsimp [g]
    field_simp
    ring
  have hm : MonotoneOn g (Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (fun r hr => (hg r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hg r (interior_subset hr)).hasDerivWithinAt)
    intro r hr
    positivity
  have h := hm (by norm_num : (0 : ℝ) ∈ Ico 0 1) hr hr.1
  simpa [g, logRatio, sub_nonneg] using h

private lemma radial_deriv {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt radialEntropy (-logRatio (Real.sqrt u) / (4 * Real.sqrt u)) u := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu.1
  have hs1 : Real.sqrt u < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith [hu.2])
  have hp0 : (1 + Real.sqrt u) / 2 ≠ 0 := by positivity
  have hp1 : (1 + Real.sqrt u) / 2 ≠ 1 := by linarith
  have h := (Real.hasDerivAt_binEntropy hp0 hp1).comp u
    (((Real.hasDerivAt_sqrt hu.1.ne').const_add 1).div_const 2)
  convert h using 1
  dsimp [logRatio]
  rw [show 1 - (1 + Real.sqrt u) / 2 = (1 - Real.sqrt u) / 2 by ring,
    Real.log_div (by linarith : 1 - Real.sqrt u ≠ 0) (by norm_num),
    Real.log_div (by positivity : 1 + Real.sqrt u ≠ 0) (by norm_num)]
  ring

private lemma radial_deriv2 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u => -logRatio (Real.sqrt u) / (4 * Real.sqrt u))
      ((logRatio (Real.sqrt u) - 2 * Real.sqrt u / (1 - u)) /
        (8 * Real.sqrt u ^ 3)) u := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu.1
  have hs1 : Real.sqrt u < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith [hu.2])
  have hsq := Real.sq_sqrt hu.1.le
  have hd : 1 - u ≠ 0 := by linarith [hu.2]
  have h := (((logRatio_deriv ⟨by linarith, hs1⟩).comp u
    (Real.hasDerivAt_sqrt hu.1.ne')).neg).div
      ((Real.hasDerivAt_sqrt hu.1.ne').const_mul 4) (by positivity : 4 * Real.sqrt u ≠ 0)
  convert h using 1
  field_simp
  nlinarith [hsq]

private lemma radial_concave : ConcaveOn ℝ (Icc (0 : ℝ) 1) radialEntropy := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
    ((Real.binEntropy_continuous.comp (by fun_prop)).continuousOn)
    (fun u hu => (radial_deriv (by simpa using hu)).hasDerivWithinAt)
    (fun u hu => (radial_deriv2 (by simpa using hu)).hasDerivWithinAt)
  intro u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := by simpa using hu
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu'.1
  have hs1 : Real.sqrt u < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith [hu'.2])
  have h := logRatio_bound ⟨hs.le, hs1⟩
  rw [Real.sq_sqrt hu'.1.le] at h
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (by positivity)

private lemma radial_antitone : AntitoneOn radialEntropy (Icc (0 : ℝ) 1) := by
  intro u hu v hv huv
  apply Real.binEntropy_strictAntiOn.antitoneOn
    ⟨by linarith [Real.sqrt_nonneg u], by nlinarith [Real.sq_sqrt hu.1, Real.sqrt_nonneg u]⟩
    ⟨by linarith [Real.sqrt_nonneg v], by nlinarith [Real.sq_sqrt hv.1, Real.sqrt_nonneg v]⟩
  exact (add_le_add_left (Real.sqrt_le_sqrt huv) 1).trans_eq (by ring)

/-- Scalar curvature estimate used by the actual qubit spectral bridge. -/
private lemma radial_contraction {x z t : ℝ} (hdisk : x ^ 2 + z ^ 2 ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ radialEntropy (x ^ 2) - radialEntropy (x ^ 2 + t ^ 2 * z ^ 2) ∧
    radialEntropy (x ^ 2) - radialEntropy (x ^ 2 + t ^ 2 * z ^ 2) ≤
      t ^ 2 * (radialEntropy (x ^ 2) - radialEntropy (x ^ 2 + z ^ 2)) := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hx : x ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg x, by nlinarith [sq_nonneg z]⟩
  have hxz : x ^ 2 + z ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨by positivity, hdisk⟩
  have hmid : x ^ 2 + t ^ 2 * z ^ 2 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht2) (sq_nonneg z)]
  constructor
  · exact sub_nonneg.mpr (radial_antitone hx hmid (by nlinarith [sq_nonneg t, sq_nonneg z]))
  · have hc := radial_concave.2 hx hxz (show 0 ≤ 1 - t ^ 2 by linarith) (sq_nonneg t)
      (by ring : (1 - t ^ 2) + t ^ 2 = 1)
    have he : (1 - t ^ 2) * x ^ 2 + t ^ 2 * (x ^ 2 + z ^ 2) = x ^ 2 + t ^ 2 * z ^ 2 := by ring
    simp only [smul_eq_mul, he] at hc
    nlinarith

end D5.S3.Quantum.Information.QubitEntropyContraction
