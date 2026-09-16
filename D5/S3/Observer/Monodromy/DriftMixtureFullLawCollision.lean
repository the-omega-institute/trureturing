/- GID: D5/S3/Observer/Monodromy/DriftMixtureFullLawCollision
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/DriftMixtureFullLawCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two distinct covariance candidates have identical complete setting-wise finite variance laws under bounded positive five-scenario drift. -/

import D5.S3.Observer.Monodromy.GainRobustGaussianDiscrimination
import Mathlib.Tactic

/-!
# A full-marginal collision beyond the second-moment obstruction

The records below are the actual records of GainRobustGaussianDiscrimination,
not an independently supplied observation table. Five equally weighted drift
scenarios suffice: c=1 and c=1/5 have the same variance multiset separately for
each of the four settings. Detector gain is exactly one, additive variance
noise lies in [0,3], and every pulse gain lies in [1/353,705/353]. In particular
all pulse gains are strictly positive in a single GainBox of half-width < 1.

The conclusion quantifies over EVERY real test function of each setting's
conditional variance. Thus it applies to every Gaussian characteristic-function
value, every Gaussian CDF value, and every conditional even moment. Those measure
interpretations are ordinary consequences, not Lean Gaussian-measure theorems.
The four permutations differ. No common permutation of entire scenario rows,
joint four-setting law, or time-labelled observation collision is asserted.

This gives one explicit nonidentifiable point in the full-law model, not the
sharp smallest drift radius or the minimal number of scenarios. The construction
uses positive, bounded, calibration-correlated additive detector noise. It must
not be claimed as a zero-noise or setting-dependent-drift counterexample.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.DriftMixtureFullLawCollision

open D5.S3.Observer.Monodromy.GainRobustGaussianDiscrimination
open D5.S3.Observer.Monodromy.TwoPulseCovarianceTomography
open D5.S3.Observer.Monodromy.TransvectionLieFiltration

/-- An explicit physically admissible five-scenario collision of all separate
conditional-variance laws. Applying any fixed variance-to-output channel to
both sides preserves the equality. The per-setting permutations are constructed
inside the proof; no collision or matching table is assumed as an input. -/
theorem five_scenario_full_marginal_collision :
    ∃ (noise sHi tHi sLo tLo : Fin 5 → ℝ),
      (∀ r, 0 ≤ noise r ∧ noise r ≤ 3 ∧
        GainBox (352/353) (sHi r) (tHi r) ∧
        GainBox (352/353) (sLo r) (tLo r)) ∧
      ∀ (k : Fin 4) (f : ℝ → ℝ),
        (∑ r, f (records 1 1 (noise r) (sHi r) (tHi r) k)) =
        ∑ r, f (records (1/5) 1 (noise r) (sLo r) (tLo r) k) := by
  classical
  -- Two elementary conics parameterize the nontrivial switching construction.
  let y : ℝ := Real.sqrt 89901
  let z : ℝ := Real.sqrt 180405 - 2
  let s : ℝ := y/5 + 2*z - 201
  let L : ℝ := s^2 + 1 - 250000 - z^2
  let r : ℝ := Real.sqrt (L/48)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y^2 = 89901 := Real.sq_sqrt (by norm_num)
  have hy : 299 < y ∧ y < 300 := by constructor <;> nlinarith
  have hz0 : 0 ≤ z+2 := by
    dsimp [z]
    linarith [Real.sqrt_nonneg (180405 : ℝ)]
  have hz2 : (z+2)^2 = 180405 := by
    dsimp [z]
    simpa using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 180405)
  have hz : 422 < z ∧ z < 423 := by constructor <;> nlinarith
  have hsdef : s = y/5 + 2*z - 201 := rfl
  have hs : 702 < s ∧ s < 705 := by constructor <;> linarith [hy.1, hy.2, hz.1, hz.2]
  have hLdef : L = s^2 + 1 - 250000 - z^2 := rfl
  have hL : 63876 < L ∧ L < 68942 := by
    constructor <;> nlinarith [hs.1, hs.2, hz.1, hz.2]
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = L/48 := Real.sq_sqrt (by linarith [hL.1])
  have hr : 36 < r ∧ r < 38 := by constructor <;> nlinarith [hL.1, hL.2]
  -- The same noise scenario array is used under both hypotheses.
  let noise : Fin 5 → ℝ :=
    ![L/2, 0, L+250197, L+249999, L] / 124609
  let SH : Fin 5 → ℝ := ![r, s, 1, 1, r]
  let TH : Fin 5 → ℝ := ![1, 1, 1, 300, 1]
  let SL : Fin 5 → ℝ := ![5*r, 5*r, 1, z, 500]
  let TL : Fin 5 → ℝ := ![1, 1, y, 10, 1]
  let sHi : Fin 5 → ℝ := fun j => SH j / 353
  let tHi : Fin 5 → ℝ := fun j => TH j / 353
  let sLo : Fin 5 → ℝ := fun j => SL j / 353
  let tLo : Fin 5 → ℝ := fun j => TL j / 353
  have scale_box (u v : ℝ) (hu : 1 ≤ u ∧ u ≤ 705) (hv : 1 ≤ v ∧ v ≤ 705) :
      GainBox (352/353) (u/353) (v/353) := by
    dsimp [GainBox]
    constructor <;> constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  have hbSH : ∀ j, 1 ≤ SH j ∧ SH j ≤ 705 := by
    intro j
    fin_cases j <;> simp [SH] <;> constructor <;> linarith [hr.1, hr.2, hs.1, hs.2]
  have hbTH : ∀ j, 1 ≤ TH j ∧ TH j ≤ 705 := by
    intro j
    fin_cases j <;> norm_num [TH]
  have hbSL : ∀ j, 1 ≤ SL j ∧ SL j ≤ 705 := by
    intro j
    fin_cases j <;> simp [SL] <;> constructor <;> linarith [hr.1, hr.2, hz.1, hz.2]
  have hbTL : ∀ j, 1 ≤ TL j ∧ TL j ≤ 705 := by
    intro j
    fin_cases j <;> simp [TL] <;> constructor <;> linarith [hy.1, hy.2]
  have hnoise : ∀ j, 0 ≤ noise j ∧ noise j ≤ 3 := by
    intro j
    fin_cases j <;> dsimp [noise] <;> constructor <;> linarith [hL.1, hL.2]
  -- Derive the scalar record formula from the previously defined pulse matrices.
  have ray (u v : ℝ) : controlledDirection u v = ![1, u, 0, v] := by
    ext j
    fin_cases j <;>
      norm_num [controlledDirection, dualPulse, increment, pairing,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply] <;> ring
  have variance_formula (c u v : ℝ) : outputVariance c u v =
      1+u^2+2*c*u*v+2*v^2 := by
    simp [outputVariance, ray, covariance, Fin.sum_univ_succ]
    <;> ring
  have record_formula (c o u v : ℝ) : records c 1 o (u/353) (v/353) =
      ![1+o, 1+o+u^2/124609, 1+o+2*v^2/124609,
        1+o+(u^2+2*c*u*v+2*v^2)/124609] := by
    ext j
    fin_cases j <;> simp [records, variance_formula] <;> ring
  let hi : Fin 5 → Fin 4 → ℝ := fun j =>
    records 1 1 (noise j) (sHi j) (tHi j)
  let lo : Fin 5 → Fin 4 → ℝ := fun j =>
    records (1/5) 1 (noise j) (sLo j) (tLo j)
  -- A different row permutation in each measurement channel.
  let perm : Fin 4 → Fin 5 → Fin 5 :=
    ![![0,1,2,3,4], ![4,0,2,1,3], ![0,1,3,2,4], ![4,0,1,3,2]]
  have matched : ∀ (j : Fin 5) (k : Fin 4), lo j k = hi (perm k j) k := by
    intro j k
    dsimp [lo, hi, sHi, tHi, sLo, tLo]
    rw [record_formula, record_formula]
    fin_cases j <;> fin_cases k <;>
      norm_num [noise, SH, TH, SL, TL, perm] <;>
      nlinarith [hy2, hz2, hr2, hsdef, hLdef]
  refine ⟨noise, sHi, tHi, sLo, tLo, ?_, ?_⟩
  · intro j
    exact ⟨(hnoise j).1, (hnoise j).2,
      scale_box _ _ (hbSH j) (hbTH j), scale_box _ _ (hbSL j) (hbTL j)⟩
  · intro k f
    change (∑ j, f (hi j k)) = ∑ j, f (lo j k)
    simp_rw [matched]
    fin_cases k <;> simp [perm, Fin.sum_univ_succ] <;> abel

#print axioms five_scenario_full_marginal_collision

end D5.S3.Observer.Monodromy.DriftMixtureFullLawCollision
