/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtWindowPhase
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/MangoldtWindowPhase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded-gap phase returns exclude subcritical Mangoldt windows. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows
import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

/-! Bounded gaps for the actual Mangoldt phase and the subcritical window obstruction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open scoped Topology BigOperators
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (G)
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open private phase phaseSum phaseSum_continuous phaseSum_one phaseSum_pow normalizedH from
  D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

namespace D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtWindowPhase

/-- The positive powers of an element of a compact group return to each identity
neighborhood with bounded gaps. -/
private theorem bounded_returns {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] (g : A) {U : Set A} (hU : IsOpen U) (h1 : 1 ∈ U) :
    ∃ L : ℕ, ∀ n : ℕ, ∃ k ≤ L, g ^ (n + k) ∈ U := by
  classical
  let H := (Subgroup.zpowers g).topologicalClosure
  let V (i : ℕ) : Set A := (fun x => x * g ^ i) ⁻¹' U
  have hcover : (H : Set A) ⊆ ⋃ i, V i := by
    intro x hx
    have hc : MapClusterPt x⁻¹ atTop (fun i : ℕ => g ^ i) :=
      mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers.mpr (H.inv_mem hx)
    have hmem : (fun z => x * z) ⁻¹' U ∈ 𝓝 x⁻¹ :=
      (hU.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using h1)
    obtain ⟨i, hi⟩ := (hc.frequently hmem).exists
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨s, hs⟩ := (Subgroup.zpowers g).isClosed_topologicalClosure.isCompact.elim_finite_subcover
    V (fun _ => hU.preimage (continuous_id.mul continuous_const)) hcover
  refine ⟨s.sup id, fun n => ?_⟩
  have hg : g ^ n ∈ H :=
    H.pow_mem ((Subgroup.zpowers g).le_topologicalClosure (Subgroup.mem_zpowers g)) n
  obtain ⟨k, h⟩ := mem_iUnion.mp (hs hg)
  obtain ⟨hk, hv⟩ := mem_iUnion.mp h
  exact ⟨k, Finset.le_sup (f := id) hk, (pow_add g n k) ▸ hv⟩

/-- In logarithmic time, every sufficiently late integer interval of a bounded
length sees a normalized Mangoldt value within delta of the first Li mass. -/
private theorem eventual_bounded_peak (rh : RiemannHypothesis) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L N : ℕ, ∀ n ≥ N, ∃ k ≤ L,
      |G ((n + k : ℕ) : ℝ) - firstLiMass| < δ := by
  let U := phaseSum ⁻¹' Metric.ball (firstLiMass : ℂ) (δ / 2)
  have hopen : IsOpen U := Metric.isOpen_ball.preimage (phaseSum_continuous rh)
  have hone : 1 ∈ U := by
    change phaseSum 1 ∈ Metric.ball _ _
    rw [phaseSum_one]
    exact Metric.mem_ball_self (half_pos hδ)
  obtain ⟨L, hit⟩ := bounded_returns phase hopen hone
  have hz := RHSharpActualEnvelope.G_sub_normalized_actualH_tendsto_zero.comp
    tendsto_natCast_atTop_atTop
  have hsmall := hz.eventually (Metric.ball_mem_nhds _ (half_pos hδ))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨L, N, fun n hn => ?_⟩
  obtain ⟨k, hk, h⟩ := hit n
  let j := n + k
  change phaseSum (phase ^ j) ∈ Metric.ball _ _ at h
  rw [phaseSum_pow rh, Metric.mem_ball, dist_eq_norm] at h
  have hre := (Complex.abs_re_le_norm (normalizedH (j : ℝ) - (firstLiMass : ℂ))).trans_lt h
  simp only [Complex.sub_re, Complex.ofReal_re, normalizedH, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
  have hres := hN j (hn.trans (Nat.le_add_right _ _))
  change dist (G (j : ℝ) - Real.exp (-(j : ℝ) / 2) * (actualH (j : ℝ)).re) 0 < δ / 2 at hres
  rw [Real.dist_eq, sub_zero] at hres
  refine ⟨k, hk, ?_⟩
  change |G (j : ℝ) - firstLiMass| < δ
  calc
    _ ≤ |G (j : ℝ) - Real.exp (-(j : ℝ) / 2) * (actualH (j : ℝ)).re|
        + |Real.exp (-(j : ℝ) / 2) * (actualH (j : ℝ)).re - firstLiMass| := abs_sub_le _ _ _
    _ < δ := by linarith

/-- Every integer interval of a fixed length contains a phase return of the normalized
Mangoldt remainder within the prescribed positive tolerance of the first Li mass. -/
theorem bounded_gap_actual_G_peak (rh : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : ℕ, ∀ n : ℕ, ∃ k ≤ L, |G ((n + k : ℕ) : ℝ) - firstLiMass| < δ := by
  obtain ⟨L, N, h⟩ := eventual_bounded_peak rh δ hδ
  refine ⟨N + L, fun n => ?_⟩
  obtain ⟨k, hk, v⟩ := h (max n N) (le_max_right _ _)
  refine ⟨max n N + k - n, by omega, ?_⟩
  rwa [show n + (max n N + k - n) = max n N + k by omega]

private theorem peak_in_every_window (rh : RiemannHypothesis) {δ b : ℝ} (hδ : 0 < δ) (hb : 1 < b) :
    ∀ᶠ Y : ℝ in atTop, ∃ x ∈ Set.Icc Y (Y ^ b), (firstLiMass - δ) * Real.sqrt x < U x := by
  obtain ⟨L, H⟩ := bounded_gap_actual_G_peak rh hδ
  have hpos : 0 < b - 1 := sub_pos.mpr hb
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (((L : ℝ) + 1) / (b - 1))] with Y hY hwide
  have hy : 0 < Y := by linarith
  have hl : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  let n := ⌈Real.log Y⌉₊
  have hlow : Real.log Y ≤ (n : ℝ) := Nat.le_ceil _
  have hhi : (n : ℝ) < Real.log Y + 1 := Nat.ceil_lt_add_one hl
  obtain ⟨k, hk, val⟩ := H n
  let j : ℝ := ((n + k : ℕ) : ℝ)
  have jdef : j = (n : ℝ) + (k : ℝ) := Nat.cast_add n k
  have hlo : Real.log Y ≤ j := by rw [jdef]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hu : j ≤ Real.log Y * b := by
    rw [jdef]
    have h1 := (div_le_iff₀ hpos).mp hwide
    have h2 : (k : ℝ) ≤ L := by exact_mod_cast hk
    nlinarith
  refine ⟨Real.exp j, ⟨(Real.exp_log hy) ▸ Real.exp_le_exp.mpr hlo, ?_⟩, ?_⟩
  · rw [Real.rpow_def_of_pos hy]
    exact Real.exp_le_exp.mpr hu
  · rw [← Real.exp_half]
    change |Real.exp (-j / 2) * U (Real.exp j) - firstLiMass| < δ at val
    have h := (abs_lt.mp val).1
    have hi : Real.exp (-j / 2) = (Real.exp (j / 2))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
    rw [hi, ← div_eq_inv_mul] at h
    exact (lt_div_iff₀ (Real.exp_pos _)).mp (by linarith)

/-- A fixed coefficient below the first Li mass cannot bound arbitrarily late
power windows, whether or not RH holds. -/
theorem no_windows_below_mass {C b : ℝ} (hC : C < firstLiMass) (hb : 1 < b) :
    ¬ (∀ R : ℝ, ∃ Y ≥ max R 2, ∀ x ∈ Set.Icc Y (Y ^ b), U x ≤ C * Real.sqrt x) := by
  intro w
  have rh : RiemannHypothesis := by
    apply (MangoldtPointwiseWindows.rh_iff_pointwise_sqrt_windows
      (C := firstLiMass + 1) (by linarith) hb).2
    intro R
    obtain ⟨Y, hY, h⟩ := w R
    exact ⟨Y, hY, fun x hx => (h x hx).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp (peak_in_every_window rh (sub_pos.mpr hC) hb)
  obtain ⟨Y, hY, h⟩ := w T
  obtain ⟨x, hx, v⟩ := hT Y ((le_max_left _ _).trans hY)
  rw [sub_sub_cancel] at v
  exact (h x hx).not_gt v

end D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtWindowPhase
