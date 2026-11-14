/- GID: D5/S3/QuantumChannels/ProjectionDiagnostics/MonitoredSpectralMean
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/ProjectionDiagnostics/MonitoredSpectralMean
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Finite dimensional monitored return and the occupied cyclic spectrum. -/

import D5.S3.QuantumChannels.ProjectionDiagnostics.CyclicMonitoredPowerBound
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.MonotoneConvergence

/-! Monitored finite sums and their cyclic operator representation. -/

noncomputable section
open scoped InnerProductSpace BigOperators
open InnerProductSpace Filter Topology

namespace D5.S3.QuantumChannels.ProjectionDiagnostics.MonitoredSpectralMean

open MonitoredReturnConservation CyclicMonitoredContraction CyclicMonitoredPowerBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

private def initial (U : E ≃ₗᵢ[ℂ] E) (v : E) : cyclicSpace U v :=
  ⟨v, initial_mem U v⟩

private def cyclicUnitary (U : E ≃ₗᵢ[ℂ] E) (v : E) :
    cyclicSpace U v ≃ₗᵢ[ℂ] cyclicSpace U v :=
  let f : cyclicSpace U v →ₗᵢ[ℂ] cyclicSpace U v :=
    { toLinearMap := U.toLinearMap.restrict (unitary_mem U v)
      norm_map' := fun x => U.norm_map (x : E) }
  LinearIsometryEquiv.ofSurjective f (LinearMap.surjective_of_injective f.injective)

private theorem unitary_coe (U : E ≃ₗᵢ[ℂ] E) (v : E) (x : cyclicSpace U v) :
    (cyclicUnitary U v x : E) = U (x : E) := rfl

private theorem step_factor (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1) :
    cyclicStep U v =
      (1 - rankOne ℂ (initial U v) (initial U v)) *
        (cyclicUnitary U v : cyclicSpace U v →L[ℂ] cyclicSpace U v) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change U (x : E) - (ℂ ∙ v).starProjection (U (x : E)) =
    U (x : E) - (inner ℂ v (U (x : E))) • v
  rw [Submodule.starProjection_singleton, hv]
  simp

private theorem right_defect (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1) :
    1 - cyclicStep U v * star (cyclicStep U v) =
      rankOne ℂ (initial U v) (initial U v) := by
  let P := rankOne ℂ (initial U v) (initial U v)
  let W : cyclicSpace U v →L[ℂ] cyclicSpace U v := cyclicUnitary U v
  have hP : star P = P := by simp [P, ContinuousLinearMap.star_eq_adjoint]
  have hPP : P * P = P := by
    exact isIdempotentElem_rankOne_self (by simpa [initial] using hv)
  have hWW : W * star W = 1 := by
    ext x
    simp [W, mul_apply_eq_comp]
  rw [step_factor U v hv]
  change 1 - ((1 - P) * W) * star ((1 - P) * W) = P
  rw [star_mul, star_sub, star_one, hP]
  calc
    1 - ((1 - P) * W) * (star W * (1 - P)) =
        1 - (1 - P) * (W * star W) * (1 - P) := by noncomm_ring
    _ = P := by rw [hWW]; noncomm_ring [hPP]

private theorem gramian_telescope (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1)
    (H : ℕ) :
    (∑ n ∈ Finset.range H,
      rankOne ℂ ((cyclicStep U v ^ n) (initial U v))
        ((cyclicStep U v ^ n) (initial U v))) =
      1 - cyclicStep U v ^ H * star (cyclicStep U v ^ H) := by
  let A := cyclicStep U v
  have hterm (n : ℕ) :
      rankOne ℂ ((A ^ n) (initial U v)) ((A ^ n) (initial U v)) =
        A ^ n * star (A ^ n) - A ^ (n + 1) * star (A ^ (n + 1)) := by
    calc
      _ = A ^ n * rankOne ℂ (initial U v) (initial U v) * star (A ^ n) := by
        simp only [ContinuousLinearMap.mul_def, comp_rankOne, rankOne_comp]
        simp only [← ContinuousLinearMap.star_eq_adjoint, star_star]
      _ = _ := by rw [← right_defect U v hv, pow_succ, star_mul]; noncomm_ring
  change (∑ n ∈ Finset.range H, rankOne ℂ ((A ^ n) (initial U v))
    ((A ^ n) (initial U v))) = 1 - A ^ H * star (A ^ H)
  simp_rw [hterm]
  rw [Finset.sum_range_sub']
  simp

private theorem trace_survival (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1)
    (H : ℕ) :
    ∑ n ∈ Finset.range H, survivalProbability U v n =
      (Module.finrank ℂ (cyclicSpace U v) : ℝ) -
        (LinearMap.trace ℂ (cyclicSpace U v)
          ((cyclicStep U v ^ H * star (cyclicStep U v ^ H)).toLinearMap)).re := by
  have h := congrArg
    (fun X : cyclicSpace U v →L[ℂ] cyclicSpace U v =>
      (LinearMap.trace ℂ (cyclicSpace U v) X.toLinearMap).re)
    (gramian_telescope U v hv H)
  have hn (n : ℕ) : ‖(cyclicStep U v ^ n) (initial U v)‖ ^ 2 =
      survivalProbability U v n := by
    change ‖((cyclicStep U v ^ n) (initial U v) : E)‖ ^ 2 = _
    rw [step_pow_coe]
    rfl
  have htr (n : ℕ) :
      (LinearMap.trace ℂ (cyclicSpace U v)
        (rankOne ℂ ((cyclicStep U v ^ n) (initial U v))
          ((cyclicStep U v ^ n) (initial U v))).toLinearMap).re =
        survivalProbability U v n := by
    rw [trace_rankOne, inner_self_eq_norm_sq_to_K]
    exact_mod_cast hn n
  simpa only [ContinuousLinearMap.toLinearMap_sum, map_sum,
    ContinuousLinearMap.toLinearMap_sub, map_sub, ContinuousLinearMap.toLinearMap_one,
    LinearMap.trace_one, Complex.natCast_re, Complex.re_sum, Complex.sub_re, htr] using h


private theorem weighted_finite (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1)
    (H : ℕ) :
    ∑ n ∈ Finset.range H, (n + 1 : ℝ) * returnProbability U v (n + 1) =
      (∑ n ∈ Finset.range H, survivalProbability U v n) -
        H * survivalProbability U v H := by
  have hp := (monitored_return_conservation U v hv).2.1
  induction H with
  | zero => simp
  | succ H ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hp H]
    push_cast
    ring

private theorem mean_cyclic_dimension (U : E ≃ₗᵢ[ℂ] E) (v : E) (hv : ‖v‖ = 1) :
    HasSum (fun n : ℕ => (n + 1 : ℝ) * returnProbability U v (n + 1))
      (Module.finrank ℂ (cyclicSpace U v) : ℝ) := by
  let C := cyclicSpace U v
  let A := cyclicStep U v
  have he_ne : initial U v ≠ 0 := by
    intro h
    have hnorm : ‖initial U v‖ = 1 := hv
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  haveI : Nontrivial C := ⟨⟨initial U v, 0, he_ne⟩⟩
  obtain ⟨N, hN, q, hq0, hq1, hq⟩ := cyclic_power_contraction U v hv
  have hnorm (k : ℕ) : ‖A ^ (k * N)‖ ≤ q ^ k := by
    calc
      ‖A ^ (k * N)‖ = ‖(A ^ N) ^ k‖ := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ ‖A ^ N‖ ^ k := norm_pow_le _ _
      _ ≤ q ^ k := pow_le_pow_left₀ (norm_nonneg _) hq _
  have hlimA : Tendsto (fun k : ℕ => A ^ (k * N)) atTop (𝓝 0) :=
    squeeze_zero_norm hnorm (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
  have hsurv (k : ℕ) : survivalProbability U v (k * N) ≤ (q ^ 2) ^ k := by
    have he : ‖initial U v‖ = 1 := hv
    have h := (A ^ (k * N)).le_opNorm (initial U v)
    rw [he, mul_one] at h
    have hs : survivalProbability U v (k * N) = ‖(A ^ (k * N)) (initial U v)‖ ^ 2 := by
      change _ = ‖((A ^ (k * N)) (initial U v) : E)‖ ^ 2
      rw [step_pow_coe]
      rfl
    rw [hs]
    calc
      _ ≤ (q ^ k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h.trans (hnorm k)) _
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hq2 : q ^ 2 < 1 := by nlinarith
  have htail : Tendsto (fun k : ℕ => (k * N : ℕ) * survivalProbability U v (k * N))
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero (fun k => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (fun k => ?_)
      (show Tendsto (fun k : ℕ => (N : ℝ) * ((k : ℝ) * (q ^ 2) ^ k))
        atTop (𝓝 0) by
        simpa using (tendsto_self_mul_const_pow_of_lt_one (sq_nonneg q) hq2).const_mul
          (N : ℝ))
    have hb := mul_le_mul_of_nonneg_left (hsurv k)
      (show 0 ≤ ((k * N : ℕ) : ℝ) by positivity)
    convert hb using 1 <;> simp only [Nat.cast_mul, survivalProbability] <;> ring
  let tr : (C →L[ℂ] C) →ₗ[ℂ] ℂ :=
    (LinearMap.trace ℂ C).comp
      (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := C) (F' := C)).symm.toLinearMap
  have htrace : Tendsto (fun k : ℕ =>
      (LinearMap.trace ℂ C ((A ^ (k * N) * star (A ^ (k * N))).toLinearMap)).re)
      atTop (𝓝 0) := by
    have ht := tr.continuous_of_finiteDimensional.tendsto 0
    have hm := hlimA.mul hlimA.star
    have ht' := ht.comp (show Tendsto
      (fun k : ℕ => A ^ (k * N) * star (A ^ (k * N))) atTop (𝓝 0) by simpa using hm)
    simpa [tr, Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp ht'
  have hp (n : ℕ) : 0 ≤ (n + 1 : ℝ) * returnProbability U v (n + 1) :=
    mul_nonneg (by positivity) (sq_nonneg _)
  apply (hasSum_iff_tendsto_nat_of_nonneg hp _).mpr
  have hmono : Monotone (fun H : ℕ => ∑ n ∈ Finset.range H,
      (n + 1 : ℝ) * returnProbability U v (n + 1)) := by
    apply monotone_nat_of_le_succ
    intro H
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hp H)
  have hcofinal : Tendsto (fun k : ℕ => k * N) atTop atTop :=
    tendsto_id.atTop_mul_const' (by omega)
  apply (tendsto_iff_tendsto_subseq_of_monotone hmono hcofinal).mpr
  have ht : Tendsto (fun k : ℕ =>
      (Module.finrank ℂ C : ℝ) -
        (LinearMap.trace ℂ C ((A ^ (k * N) * star (A ^ (k * N))).toLinearMap)).re -
        (k * N : ℕ) * survivalProbability U v (k * N))
      atTop (𝓝 (Module.finrank ℂ C : ℝ)) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds (x := (Module.finrank ℂ C : ℝ))).sub htrace).sub htail
  convert ht using 1
  funext k
  exact (weighted_finite U v hv (k * N)).trans
    (congrArg (fun x : ℝ => x - (k * N : ℕ) * survivalProbability U v (k * N))
      (trace_survival U v hv (k * N)))

end D5.S3.QuantumChannels.ProjectionDiagnostics.MonitoredSpectralMean
