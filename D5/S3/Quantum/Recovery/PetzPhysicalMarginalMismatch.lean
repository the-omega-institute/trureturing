/- GID: D5/S3/Quantum/Recovery/PetzPhysicalMarginalMismatch
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/PetzPhysicalMarginalMismatch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A strictly positive retained-marginal mismatch at every faithful reference spectrum. -/

import D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation

/-! The positive retained-marginal derivative defect for every faithful reference spectrum. -/

noncomputable section

open Matrix
open scoped Matrix.Norms.Elementwise
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Recovery.BKMFlagRefinement (partialTracePetz marginal marginal_eq_sum)
open D5.S3.Quantum.Recovery.PetzPhysicalFirstVariation
open D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot (qubit)

namespace D5.S3.Quantum.Recovery.PetzPhysicalMarginalMismatch

private theorem retainedEntry_eq (t ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 16)
    (hη : 0 < η) :
    (partialTraceRight (recoveryVariation t ε η) 0 1).re =
      let B := Real.sqrt (1 - ε ^ 2)
      B * (1 - t - t) - 2 * ε ^ 2 * (1 - t - t * η ^ 2) / (B * (η ^ 2 + 1) + 2 * η) := by
  let u := Real.sqrt (1 - ε)
  let v := Real.sqrt (1 + ε)
  have hu : 0 < u := Real.sqrt_pos.2 (by linarith)
  have hv : 0 < v := Real.sqrt_pos.2 (by linarith)
  have hu2 : u ^ 2 = 1 - ε := Real.sq_sqrt (le_of_lt (by linarith))
  have hv2 : v ^ 2 = 1 + ε := Real.sq_sqrt (le_of_lt (by linarith))
  have hB : Real.sqrt (1 - ε ^ 2) = u * v := by
    have he : 1 - ε ^ 2 = (1 - ε) * (1 + ε) := by ring
    rw [he, Real.sqrt_mul (by linarith)]
  change (marginal _ 0 1).re = _
  rw [marginal_eq_sum]
  simp only [Matrix.sum_apply, Fin.sum_univ_two, Complex.add_re]
  change recoveryEntry t ε η + recoveryEntry t (-ε) η = _
  unfold recoveryEntry
  simp only [sub_neg_eq_add, add_neg_eq_sub, hB]
  change u * v * (1 - t - t) / 2 + ε * ((1 - t) * u + t * η * v) / (η * u + v) +
      (v * u * (1 - t - t) / 2 + -ε * ((1 - t) * v + t * η * u) / (η * v + u)) =
    u * v * (1 - t - t) - 2 * ε ^ 2 * (1 - t - t * η ^ 2) / (u * v * (η ^ 2 + 1) + 2 * η)
  have hp : 0 < η * u + v := by positivity
  have hm : 0 < η * v + u := by positivity
  have hprod : (η * u + v) * (η * v + u) = u * v * (η ^ 2 + 1) + 2 * η := by
    nlinarith only [congrArg (fun w : ℝ => η * w) hu2, congrArg (fun w : ℝ => η * w) hv2]
  have hnum :
      ((1 - t) * u + t * η * v) * (η * v + u) -
        ((1 - t) * v + t * η * u) * (η * u + v) =
      (1 - t - t * η ^ 2) * (-2 * ε) := by
    calc
      _ = (1 - t - t * η ^ 2) * (u ^ 2 - v ^ 2) := by ring
      _ = _ := by rw [hu2, hv2]; ring
  rw [← hprod, show
    u * v * (1 - t - t) / 2 + ε * ((1 - t) * u + t * η * v) / (η * u + v) +
      (v * u * (1 - t - t) / 2 + -ε * ((1 - t) * v + t * η * u) / (η * v + u)) =
    u * v * (1 - t - t) + ε * ((((1 - t) * u + t * η * v) / (η * u + v)) -
      (((1 - t) * v + t * η * u) / (η * v + u))) by ring,
    div_sub_div _ _ hp.ne' hm.ne', hnum]
  ring

/-- The mismatch is the derivative of the actual source-minus-recovered marginal.
The lower bound is independent of the positive reference eigenvalue ratio. -/
theorem physical_marginal_mismatch {t ε η : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 16) (hη : 0 < η) :
    let B := Real.sqrt (1 - ε ^ 2)
    let μ := 1 - t - t - (partialTraceRight (recoveryVariation t ε η) 0 1).re
    HasDerivAt (fun c =>
      (sourceMarginal t c 0 1 -
        partialTraceRight (partialTracePetz (reference ε η c) (sourceMarginal t c)) 0 1).re) μ 0 ∧
      μ = (1 - B) * (1 - t - t) +
        2 * ε ^ 2 * (1 - t - t * η ^ 2) / (B * (η ^ 2 + 1) + 2 * η) ∧
      ε ^ 2 / 10 ≤ μ ∧ 0 < μ := by
  dsimp only
  obtain ⟨hT, hP⟩ := physical_firstVariation t hε hε' hη
  have hm : HasDerivAt
      (fun c => partialTraceRight (partialTracePetz (reference ε η c) (sourceMarginal t c)) 0 1)
      (partialTraceRight (recoveryVariation t ε η) 0 1) 0 := by
    exact HasDerivAt.fun_sum fun s _ => hasDerivAt_pi.mp (hasDerivAt_pi.mp hT (0, s)) (1, s)
  have hsource : HasDerivAt (fun c => sourceMarginal t c 0 1) ((1 - t - t : ℝ) : ℂ) 0 := by
    simpa [qubit] using hasDerivAt_pi.mp (hasDerivAt_pi.mp hP 0) 1
  have hdiff := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hsource.sub hm))
  let B := Real.sqrt (1 - ε ^ 2)
  have hBsq : B ^ 2 = 1 - ε ^ 2 := Real.sq_sqrt (by nlinarith)
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hB : 15 / 16 ≤ B := by
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr hε') (show 0 ≤ 1 / 16 + ε by positivity),
      mul_pos (sub_pos.mpr h) (show 0 < 15 / 16 + B by positivity)]
  have hB1 : B ≤ 1 := by nlinarith
  have hBp : 0 < B := by linarith
  have hD : 0 < B * (η ^ 2 + 1) + 2 * η := by positivity
  have hr : -(t / B) ≤ (1 - t - t * η ^ 2) / (B * (η ^ 2 + 1) + 2 * η) := by
    rw [le_div_iff₀ hD]
    have hmul : (t / B) * (B * (η ^ 2 + 1) + 2 * η) =
        t * (η ^ 2 + 1) + (t / B) * (2 * η) := by
      field_simp [hBp.ne']
    rw [neg_mul, hmul]
    nlinarith only [show 0 ≤ (t / B) * (2 * η) by positivity]
  have hidentity : (1 - B) = ε ^ 2 / (1 + B) := by
    rw [eq_div_iff (by positivity)]
    nlinarith
  have hleft : 3 / 8 ≤ (1 - t - t) / (1 + B) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hright : 2 * (t / B) ≤ 4 / 15 := by
    rw [← mul_div_assoc, div_le_iff₀ hBp]
    linarith
  have he := retainedEntry_eq t ε η hε hε' hη
  change _ = B * _ - _ at he
  have hf : 1 / 10 ≤ (1 - t - t) / (1 + B) +
      2 * ((1 - t - t * η ^ 2) / (B * (η ^ 2 + 1) + 2 * η)) := by linarith
  have hlow : ε ^ 2 / 10 ≤ 1 - t - t - (partialTraceRight (recoveryVariation t ε η) 0 1).re := by
    rw [he]
    calc
      ε ^ 2 / 10 = ε ^ 2 * (1 / 10) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hf (sq_nonneg ε)
      _ = _ := by
        rw [← div_mul_eq_mul_div, ← hidentity]
        ring
  exact ⟨by simpa [Complex.sub_re] using hdiff, by rw [he]; ring, hlow,
    (show 0 < ε ^ 2 / 10 by positivity).trans_le hlow⟩

end D5.S3.Quantum.Recovery.PetzPhysicalMarginalMismatch
