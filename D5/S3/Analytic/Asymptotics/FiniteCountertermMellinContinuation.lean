/- GID: D5/S3/Analytic/Asymptotics/FiniteCountertermMellinContinuation
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/FiniteCountertermMellinContinuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Mellin counterterms extend the transform meromorphically. -/

/- Library-search audit trail (2026-08-28):
* Searches for Mellin, counterterm, regularization, pole-term, and meromorphic-integral shapes in
  `D5/**/*.lean` found completed-zeta specializations and Mellin dilation identities, but no theorem
  giving the general finite-counterterm continuation on a variable heat trace.
* `D5.S3.Analytic.CompletedZetaMellinReconstruction` is a fixed theta-kernel specialization and is
  not an exact hit for the source carrier or its finite family of counterterms.
* Pinned Mathlib's `mellin_differentiableAt_of_isBigO_rpow_exp` supplies holomorphy of the
  regularized Mellin integral, and `hasMellin_cpow_Ioc` evaluates each subtracted local power.
  `MeromorphicOn.fun_sum`, `.add`, `.div`, and `.congr` supply the finite pole sum and transfer the
  result to the source's split-integral formula. All are applied directly below.
-/

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Basic

open Asymptotics Filter MeasureTheory Set
open Complex
open scoped Topology

namespace D5.S3.Analytic.Asymptotics.FiniteCountertermMellinContinuation

noncomputable section

private theorem hasMellin_finset_sum
    {ι : Type*} {u : Finset ι} {f : ι → ℝ → ℂ} {value : ι → ℂ} {s : ℂ}
    (h : ∀ i ∈ u, HasMellin (f i) s (value i)) :
    HasMellin (fun t => ∑ i ∈ u, f i t) s (∑ i ∈ u, value i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [HasMellin, MellinConvergent, mellin]
  | @insert i u hi ih =>
      have hTerm := h i (Finset.mem_insert_self i u)
      have hTail := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have hAdd := hasMellin_add hTerm.1 hTail.1
      rw [hTerm.2, hTail.2] at hAdd
      simpa [hi] using hAdd

/-- Subtracting finitely many local power modes exposes a Mellin remainder that is holomorphic on
`alpha_m < re s`; adding the explicit rational modes gives a meromorphic continuation there and
recovers the original Mellin transform wherever the latter converges. -/
theorem finite_counterterm_mellin_continuation
    {m : ℕ} (theta : ℝ → ℂ) (a : Fin m → ℂ) (alpha : Fin (m + 1) → ℝ)
    (decay : ℝ) (hAlpha : StrictAnti alpha) (hdecay : 0 < decay)
    (hregularizedLocallyIntegrable :
      let residual : ℝ → ℂ := fun t =>
        theta t - ∑ j : Fin m, a j * (t : ℂ) ^ (-(alpha j.castSucc : ℂ))
      let regularized : ℝ → ℂ := fun t => if t ≤ 1 then residual t else theta t
      LocallyIntegrableOn regularized (Ioi 0))
    (hresidual : IsBigO (𝓝[>] (0 : ℝ))
      (fun t : ℝ => theta t - ∑ j : Fin m,
        a j * (t : ℂ) ^ (-(alpha j.castSucc : ℂ)))
      (fun t : ℝ => t ^ (-alpha (Fin.last m))))
    (hthetaTop : theta =O[atTop] fun t : ℝ => Real.exp (-decay * t)) :
    let residual : ℝ → ℂ := fun t =>
      theta t - ∑ j : Fin m, a j * (t : ℂ) ^ (-(alpha j.castSucc : ℂ))
    let M_m : ℂ → ℂ := fun s =>
      (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) * residual t) +
      (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * theta t) +
      ∑ j : Fin m, a j / (s - alpha j.castSucc)
    MeromorphicOn M_m {s | alpha (Fin.last m) < s.re} ∧
      ∀ s : ℂ, alpha 0 < s.re →
        MellinConvergent theta s ∧ M_m s = mellin theta s := by
  classical
  dsimp only at hregularizedLocallyIntegrable
  dsimp only
  let residual : ℝ → ℂ := fun t =>
    theta t - ∑ j : Fin m, a j * (t : ℂ) ^ (-(alpha j.castSucc : ℂ))
  let regularized : ℝ → ℂ := fun t => if t ≤ 1 then residual t else theta t
  let poleSum : ℂ → ℂ := fun s => ∑ j : Fin m, a j / (s - alpha j.castSucc)
  let Msplit : ℂ → ℂ := fun s =>
    (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) * residual t) +
    (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * theta t) + poleSum s
  let U : Set ℂ := {s | alpha (Fin.last m) < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hregBot : regularized =O[𝓝[>] 0] fun t : ℝ => t ^ (-alpha (Fin.last m)) := by
    apply hresidual.congr'
    · filter_upwards [
        (eventually_le_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with t ht
      simp [regularized, residual, ht]
    · exact Eventually.of_forall fun _ => rfl
  have hregTop : regularized =O[atTop] fun t : ℝ => Real.exp (-decay * t) := by
    apply hthetaTop.congr'
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      simp [regularized, not_le.mpr ht]
    · exact Eventually.of_forall fun _ => rfl
  have hregConvergent (s : ℂ) (hs : s ∈ U) : MellinConvergent regularized s :=
    mellinConvergent_of_isBigO_rpow_exp hdecay hregularizedLocallyIntegrable
      hregTop hregBot hs
  have hsplit (s : ℂ) (hs : s ∈ U) :
      Msplit s = mellin regularized s + poleSum s := by
    have hconv := hregConvergent s hs
    have hleft : IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * regularized t) (Ioc 0 1) := by
      exact hconv.mono_set Ioc_subset_Ioi_self
    have hright : IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * regularized t) (Ioi 1) := by
      exact hconv.mono_set (Ioi_subset_Ioi zero_le_one)
    dsimp only [Msplit]
    rw [mellin]
    simp only [smul_eq_mul]
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hleft hright]
    have hleftEq :
        (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) * residual t) =
          ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) * regularized t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      exact congrArg ((t : ℂ) ^ (s - 1) * ·) (by simp [regularized, ht.2])
    have hrightEq :
        (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * theta t) =
          ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * regularized t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht' : ¬t ≤ 1 := not_le.mpr (Set.mem_Ioi.mp ht)
      exact congrArg ((t : ℂ) ^ (s - 1) * ·) (by simp [regularized, ht'])
    rw [hleftEq, hrightEq]
  have hmellinDiff : DifferentiableOn ℂ (mellin regularized) U := by
    intro s hs
    exact (mellin_differentiableAt_of_isBigO_rpow_exp hdecay
      hregularizedLocallyIntegrable hregTop hregBot hs).differentiableWithinAt
  have hmellinMeromorphic : MeromorphicOn (mellin regularized) U :=
    (hmellinDiff.analyticOnNhd hU).meromorphicOn
  have hpoleMeromorphic : MeromorphicOn poleSum U := by
    apply MeromorphicOn.fun_sum
    intro j
    change MeromorphicOn (fun s : ℂ => a j / (s - (alpha j.castSucc : ℂ))) U
    intro z _
    exact (MeromorphicAt.const (a j) z).div
      ((MeromorphicAt.id z).sub (MeromorphicAt.const (alpha j.castSucc : ℂ) z))
  have hMsplitMeromorphic : MeromorphicOn Msplit U := by
    apply (hmellinMeromorphic.add hpoleMeromorphic).congr
    · intro s hs
      exact (hsplit s hs).symm
    · exact hU
  refine ⟨hMsplitMeromorphic, ?_⟩
  intro s hs
  have hsU : s ∈ U := by
    exact lt_of_le_of_lt (hAlpha.antitone (Fin.zero_le _)) hs
  have hprincipal : HasMellin
      (fun t : ℝ => ∑ j : Fin m,
        a j • (Ioc (0 : ℝ) 1).indicator
          (fun u : ℝ => (u : ℂ) ^ (-(alpha j.castSucc : ℂ))) t)
      s (poleSum s) := by
    apply hasMellin_finset_sum
    intro j _
    have hjBound : alpha j.castSucc ≤ alpha 0 :=
      hAlpha.antitone (Fin.zero_le _)
    have hj : 0 < s.re + (-(alpha j.castSucc : ℂ)).re := by
      change 0 < s.re - alpha j.castSucc
      linarith
    have hpower := hasMellin_cpow_Ioc (-(alpha j.castSucc : ℂ)) hj
    have hscaled := hasMellin_const_smul hpower.1 (a j)
    rw [hpower.2] at hscaled
    simpa [poleSum, div_eq_mul_inv, sub_eq_add_neg] using hscaled
  have hsumConvergent := hasMellin_add (hregConvergent s hsU) hprincipal.1
  have hthetaEq : Set.EqOn theta
      (fun t : ℝ => regularized t + ∑ j : Fin m,
        a j • (Ioc (0 : ℝ) 1).indicator
          (fun u : ℝ => (u : ℂ) ^ (-(alpha j.castSucc : ℂ))) t) (Ioi 0) := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · have htIoc : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
      simp [regularized, residual, ht1, Set.indicator_of_mem htIoc, smul_eq_mul]
    · simp [regularized, ht1, smul_eq_mul]
  have hthetaConvergent : MellinConvergent theta s := by
    rw [MellinConvergent]
    exact hsumConvergent.1.congr_fun (fun t ht => by
      exact congrArg ((t : ℂ) ^ (s - 1) • ·) (hthetaEq ht).symm) measurableSet_Ioi
  have hmellinEq : mellin theta s = mellin regularized s + poleSum s := by
    calc
      mellin theta s = mellin (fun t : ℝ => regularized t + ∑ j : Fin m,
          a j • (Ioc (0 : ℝ) 1).indicator
            (fun u : ℝ => (u : ℂ) ^ (-(alpha j.castSucc : ℂ))) t) s := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact congrArg ((t : ℂ) ^ (s - 1) • ·) (hthetaEq ht)
      _ = mellin regularized s + poleSum s := by
        exact hsumConvergent.2.trans (congrArg (mellin regularized s + ·) hprincipal.2)
  refine ⟨hthetaConvergent, ?_⟩
  change Msplit s = mellin theta s
  rw [hsplit s hsU, hmellinEq]

end

end D5.S3.Analytic.Asymptotics.FiniteCountertermMellinContinuation
