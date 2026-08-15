/- GID: D5/S3/RenyiDivergence/OrderOneLimit
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove finite Renyi divergence converges to KL divergence as its order tends to one. -/

import Mathlib
import D5.S3.RenyiDivergence.Basic
import D5.S3.Divergence.ClassicalDPI

/- Provenance: Native proof over pinned mathlib. -/

/- SEARCH RECEIPT (2026-08-15):
   * `Mathlib/Analysis/Calculus/Deriv/Slope.lean:73` gives
     `hasDerivAt_iff_tendsto_slope`, with source filter `nhdsWithin x {x}ᶜ`.
   * `Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:404` gives
     `Real.hasStrictDerivAt_const_rpow`, under the necessary hypothesis that its base is positive.
   * `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:128` gives `Real.zero_rpow` for a
     nonzero exponent; it is used below on the neighborhood `Ioi 0` of one.
   * `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:52` gives `Real.hasDerivAt_log` at
     a nonzero point, and `Mathlib/Analysis/Calculus/Deriv/Add.lean:218` gives the finite
     function-sum derivative rule `HasDerivAt.fun_sum`.
   * `D5/S3/RenyiDivergence/Basic.lean:36` defines `renyiDivergence`, and
     `D5/S3/Divergence/ClassicalDPI.lean:28` defines the finite real `klDivergence`.
   * `D5/S3/RenyiDivergence/OrderLimits.lean:26` explicitly leaves the topological
     order-one limit open. A search of `D5/S3` for Renyi limit/derivative declarations found
     no existing result that proves this limit.
-/

namespace D5.S3.RenyiDivergence.OrderOneLimit

open D5.S3.Divergence.ClassicalDPI

/-- Finite Renyi divergence converges to finite KL divergence through orders distinct from one.
Zero coordinates of `p` are handled as locally constant summands, so positivity of `q` is needed
only on the positive support of `p`. -/
theorem renyi_divergence_tendsto_kl {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : ∀ i, 0 < p i → 0 < q i) :
    Filter.Tendsto (fun a : ℝ => renyiDivergence a p q)
      (nhdsWithin 1 {(1 : ℝ)}ᶜ) (nhds (klDivergence p q)) := by
  classical
  let g : ℝ → ℝ := fun a => ∑ i, (p i) ^ a * (q i) ^ (1 - a)
  have hg_one : g 1 = 1 := by
    simp [g, hp.2]
  have hterm (i : ι) :
      HasDerivAt (fun a : ℝ => (p i) ^ a * (q i) ^ (1 - a))
        (p i * Real.log (p i / q i)) 1 := by
    by_cases hpi_zero : p i = 0
    · have heventually :
          (fun a : ℝ => (p i) ^ a * (q i) ^ (1 - a)) =ᶠ[nhds 1]
            (fun _ => 0) := by
          filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
          rw [hpi_zero, Real.zero_rpow ha.ne', zero_mul]
      simpa [hpi_zero] using
        (hasDerivAt_const (x := (1 : ℝ)) (c := (0 : ℝ))).congr_of_eventuallyEq
          heventually
    · have hpi : 0 < p i := lt_of_le_of_ne (hp.1 i) (Ne.symm hpi_zero)
      have hqi : 0 < q i := hq i hpi
      have hp_deriv := (Real.hasStrictDerivAt_const_rpow hpi 1).hasDerivAt
      have hlinear : HasDerivAt (fun a : ℝ => 1 - a) (-1) 1 := by
        apply HasDerivAt.const_sub
        exact hasDerivAt_id 1
      have hq_deriv :=
        (Real.hasStrictDerivAt_const_rpow hqi ((1 : ℝ) - 1)).hasDerivAt.comp 1 hlinear
      convert! hp_deriv.mul hq_deriv using 1
      simp [Real.log_div hpi.ne' hqi.ne']
      ring
  have hg : HasDerivAt g (klDivergence p q) 1 := by
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hterm i
    simpa [g, klDivergence] using hsum
  have hlog : HasDerivAt (fun a => Real.log (g a)) (klDivergence p q) 1 := by
    have h := (Real.hasDerivAt_log (show g 1 ≠ 0 by rw [hg_one]; norm_num)).comp 1 hg
    change HasDerivAt (Real.log ∘ g) (klDivergence p q) 1
    exact h.congr_deriv (by simp [hg_one])
  have hslope :
      Filter.Tendsto (slope (fun a => Real.log (g a)) 1)
        (nhdsWithin 1 {(1 : ℝ)}ᶜ) (nhds (klDivergence p q)) :=
    hasDerivAt_iff_tendsto_slope.mp hlog
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha_ne : a ≠ 1 := by simpa using ha
  rw [renyiDivergence, slope_def_field]
  simp only [g, hg_one, Real.log_one, sub_zero]
  field_simp

#print axioms renyi_divergence_tendsto_kl

end D5.S3.RenyiDivergence.OrderOneLimit
