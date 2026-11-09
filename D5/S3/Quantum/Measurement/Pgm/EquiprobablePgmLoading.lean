/- GID: D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmLoading
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Pgm/EquiprobablePgmLoading
   mirror-E: none(waiver:universal-loading-proof)
   anchors: []
   utility: none
   digest: Full physical loading domain and sharp active-set boundary. -/

import D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
Anonymous mechanism manuscript, loading regime; exact boundary and threshold
verification by Haobo Ma and Wenlin Zhang (4 November 2026, CC BY 4.0 for
that new note only). Hyunho Cha's symmetric score calculation is retained.
The mathematical content is the entire physical domain, sharp boundary and
global complement, not isolated numerical loading examples.
-/

noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmLoading
open D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmSymmetric
open D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (pgmScore success)
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation (finitePOVM)

/-- Physical loading states; no implicit admissibility or limiting convention. -/
def states (κ K t : ℝ) := rho (1 - t ^ 2) (κ * t) (1 - K * t ^ 2)

private theorem domain (κ K t : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hK : 1 < K) (ht : 0 < t) (htκ : t ^ 2 < 1 - κ ^ 2) (htK : K * t ^ 2 < 1) :
    0 < 1 - t ^ 2 ∧ 1 - t ^ 2 < 1 ∧
      0 < 1 - K * t ^ 2 ∧ 1 - K * t ^ 2 < 1 ∧
      0 < (1 - t ^ 2) * (1 - (1 - t ^ 2)) - (κ * t) ^ 2 := by
  have hp : 0 < t ^ 2 := sq_pos_of_pos ht
  have hd := mul_pos hp (show 0 < 1 - κ ^ 2 - t ^ 2 by linarith)
  refine ⟨by nlinarith [sq_nonneg κ], by linarith, by linarith, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- Equality at t=kappa/(K-1) belongs to the unique two-active optimum.
Above that boundary all three actual effects are active. -/
theorem loading_classification (κ K t : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hK : 1 < K) (ht : 0 < t) (htκ : t ^ 2 < 1 - κ ^ 2) (htK : K * t ^ 2 < 1) :
    (∀ i, (states κ K t i).PosDef ∧ trace (states κ K t i) = 1) ∧
    finitePOVM (optimalPovm (1 - t ^ 2) (κ * t) (1 - K * t ^ 2)) ∧
    (∀ E, finitePOVM E →
      ((∀ F, finitePOVM F → success (states κ K t) F ≤ success (states κ K t) E) ↔
        E = optimalPovm (1 - t ^ 2) (κ * t) (1 - K * t ^ 2))) ∧
    (Finset.univ.filter (fun i =>
      optimalPovm (1 - t ^ 2) (κ * t) (1 - K * t ^ 2) i ≠ 0)) =
        if t ≤ κ / (K - 1) then {0, 1} else Finset.univ := by
  obtain ⟨ha, ha1, hc, hc1, hd⟩ := domain κ K t hκ hκ1 hK ht htκ htK
  have hclass := complete_classification (1 - t ^ 2) (κ * t) (1 - K * t ^ 2)
    (mul_pos hκ ht)
  refine ⟨states_posDef _ _ _ ha hc hc1 hd, hclass.1, hclass.2.1, ?_⟩
  rw [hclass.2.2]
  have habs : |(1 - K * t ^ 2) - (1 - t ^ 2)| = (K - 1) * t ^ 2 := by
    rw [abs_of_nonpos (by nlinarith : (1 - K * t ^ 2) - (1 - t ^ 2) ≤ 0)]
    ring
  have hiff : |(1 - K * t ^ 2) - (1 - t ^ 2)| ≤ κ * t ↔ t ≤ κ / (K - 1) := by
    rw [habs, le_div_iff₀ (by linarith : 0 < K - 1)]
    have hcancel := mul_le_mul_iff_left₀ ht (b := (K - 1) * t) (c := κ)
    convert hcancel using 1 <;> ring
  simp only [hiff]

/-- Exact full-domain identity for the spectral ratio controlling failure. -/
theorem spectral_ratio (κ K t : ℝ) (ht : 0 < t) (ht1 : t ^ 2 < 1) :
    ((2 * (1 - t ^ 2) + (1 - K * t ^ 2)) *
      (3 - 2 * (1 - t ^ 2) - (1 - K * t ^ 2))) /
        ((1 - t ^ 2) * (1 - (1 - t ^ 2))) =
      3 * (K + 2) - (K + 2) * (K - 1) * t ^ 2 / (1 - t ^ 2) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hne : 1 - t ^ 2 ≠ 0 := by linarith
  field_simp <;> ring

/-- The entire admissible loading domain is nonviolating when 1<K<=10/3,
including the sharp threshold. The three-active region gives equality. -/
theorem global_nonviolation (κ K t : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hK : 1 < K) (hKhi : K ≤ 10 / 3) (ht : 0 < t)
    (htκ : t ^ 2 < 1 - κ ^ 2) (htK : K * t ^ 2 < 1) :
    let A := Finset.univ.filter (fun i =>
      optimalPovm (1 - t ^ 2) (κ * t) (1 - K * t ^ 2) i ≠ 0)
    ((A.card : ℝ) - 1) * (pgmScore (states κ K t) A - 1 / 3) ≤
      2 * (pgmScore (states κ K t) Finset.univ - 1 / 3) := by
  obtain ⟨ha, ha1, hc, hc1, hd⟩ := domain κ K t hκ hκ1 hK ht htκ htK
  have hf := (active_failure_iff (1 - t ^ 2) (κ * t) (1 - K * t ^ 2)
    ha ha1 (mul_pos hκ ht) hc hc1 hd).2
  dsimp only at hf ⊢
  apply le_of_not_gt
  intro hv
  have hD := (hf.mp hv).2.1
  have hratio := spectral_ratio κ K t ht (by nlinarith [sq_nonneg κ])
  have hq : 0 < (1 - t ^ 2) * (1 - (1 - t ^ 2)) := mul_pos ha (sub_pos.mpr ha1)
  have hratiohi : 16 < ((2 * (1 - t ^ 2) + (1 - K * t ^ 2)) *
      (3 - 2 * (1 - t ^ 2) - (1 - K * t ^ 2))) /
        ((1 - t ^ 2) * (1 - (1 - t ^ 2))) := (lt_div_iff₀ hq).mpr (by nlinarith)
  have hload : 0 ≤ (K + 2) * (K - 1) * t ^ 2 / (1 - t ^ 2) := by positivity
  linarith

private def scaledGap (κ K t : ℝ) : ℝ :=
  2 * κ ^ 2 / (3 * Real.sqrt (1 - t ^ 2)) -
    8 * κ ^ 2 / (3 * Real.sqrt ((K + 2) * (3 - (K + 2) * t ^ 2))) -
    4 * (K - 1) ^ 2 * t / (3 * (K + 2) * (3 - (K + 2) * t ^ 2))

private theorem actual_gap (κ K t : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hK : 1 < K) (ht : 0 < t) (htκ : t ^ 2 < 1 - κ ^ 2) (htK : K * t ^ 2 < 1) :
    (pgmScore (states κ K t) {0, 1} - 1 / 3) -
      2 * (pgmScore (states κ K t) Finset.univ - 1 / 3) = t * scaledGap κ K t := by
  obtain ⟨ha, ha1, hc, hc1, hd⟩ := domain κ K t hκ hκ1 hK ht htκ htK
  have hs := D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison.symmetric_scores
    (1 - t ^ 2) (κ * t) (1 - K * t ^ 2) ha ha1 hc hc1
  have hq : (1 - t ^ 2) * (1 - (1 - t ^ 2)) = t ^ 2 * (1 - t ^ 2) := by ring
  have hD : (2 * (1 - t ^ 2) + (1 - K * t ^ 2)) *
      (3 - 2 * (1 - t ^ 2) - (1 - K * t ^ 2)) =
        t ^ 2 * ((K + 2) * (3 - (K + 2) * t ^ 2)) := by ring
  have hqroot : Real.sqrt ((1 - t ^ 2) * (1 - (1 - t ^ 2))) =
      t * Real.sqrt (1 - t ^ 2) := by
    rw [hq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht.le]
  have hDroot : Real.sqrt ((2 * (1 - t ^ 2) + (1 - K * t ^ 2)) *
      (3 - 2 * (1 - t ^ 2) - (1 - K * t ^ 2))) =
        t * Real.sqrt ((K + 2) * (3 - (K + 2) * t ^ 2)) := by
    rw [hD, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht.le]
  change (pgmScore (rho _ _ _) _ - 1 / 3) - 2 * (pgmScore (rho _ _ _) _ - 1 / 3) = _
  rw [hs.1, hs.2, hqroot, hDroot, hD]
  dsimp [scaledGap]
  field_simp <;> ring

open Filter Topology in
private theorem small_loading (κ K : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) (hK : 1 < K) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t ∧ t ^ 2 < 1 - κ ^ 2 ∧
      K * t ^ 2 < 1 ∧ t < κ / (K - 1) := by
  have hs : (0 : ℝ) < 1 - κ ^ 2 := by nlinarith
  have hc : ContinuousAt (fun t : ℝ => t ^ 2) 0 := by fun_prop
  have hd : ContinuousAt (fun t : ℝ => K * t ^ 2) 0 := by fun_prop
  filter_upwards [self_mem_nhdsWithin,
    ((hc.tendsto.eventually_lt_const (show (0 : ℝ) ^ 2 < 1 - κ ^ 2 by simpa using hs)).filter_mono nhdsWithin_le_nhds),
    ((hd.tendsto.eventually_lt_const (by norm_num : K * (0 : ℝ) ^ 2 < 1)).filter_mono nhdsWithin_le_nhds),
    ((eventually_lt_nhds (div_pos hκ (by linarith : 0 < K - 1))).filter_mono nhdsWithin_le_nhds)] with t ht hs hd hc
  exact ⟨ht, hs, hd, hc⟩

open Filter Topology in
/-- The whole sufficiently-small positive interval violates precisely above 10/3.
The conclusion uses the actual optimal effects and their nonzero-label filter. -/
theorem sharp_threshold (κ K : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) (hK : 1 < K) :
    (∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      t ^ 2 < 1 - κ ^ 2 ∧ K * t ^ 2 < 1 ∧
      (∀ i, (states κ K t i).PosDef ∧ trace (states κ K t i) = 1) ∧
      Finset.univ.filter (fun i =>
        optimalPovm (1 - t ^ 2) (κ * t) (1 - K * t ^ 2) i ≠ 0) = {0, 1} ∧
      2 * (pgmScore (states κ K t) Finset.univ - 1 / 3) <
        pgmScore (states κ K t) {0, 1} - 1 / 3) ↔ 10 / 3 < K := by
  constructor
  · intro he
    by_contra hn
    have hhi : K ≤ 10 / 3 := le_of_not_gt hn
    have hc : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), False := by
      filter_upwards [he, small_loading κ K hκ hκ1 hK] with t ht hd
      have hg := global_nonviolation κ K t hκ hκ1 hK hhi hd.1 ht.1 ht.2.1
      dsimp only at hg
      rw [ht.2.2.2.1] at hg
      norm_num at hg
      linarith [ht.2.2.2.2]
    exact (Filter.Eventually.exists hc).elim (fun _ h => h)
  · intro hsharp
    have hroot : 4 < Real.sqrt (3 * (K + 2)) := by
      have hp : 0 < 3 * (K + 2) := by linarith
      nlinarith [Real.sq_sqrt hp.le, Real.sqrt_nonneg (3 * (K + 2))]
    have hlim : ContinuousAt (scaledGap κ K) 0 := by
      unfold scaledGap
      fun_prop (disch := norm_num <;> positivity)
    have hpos : 0 < scaledGap κ K 0 := by
      simp only [scaledGap, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero,
        Real.sqrt_one, mul_one, zero_div]
      have hs : 0 < Real.sqrt (3 * (K + 2)) := by linarith
      have hr : Real.sqrt ((K + 2) * 3) = Real.sqrt (3 * (K + 2)) := by congr 1; ring
      rw [hr]
      apply sub_pos.mpr
      apply (div_lt_iff₀ (by positivity : 0 < 3 * Real.sqrt (3 * (K + 2)))).mpr
      nlinarith [sq_pos_of_pos hκ]
    filter_upwards [small_loading κ K hκ hκ1 hK,
      (hlim.tendsto.eventually_const_lt hpos).filter_mono nhdsWithin_le_nhds] with t hd hg
    have hf := loading_classification κ K t hκ hκ1 hK hd.1 hd.2.1 hd.2.2.1
    refine ⟨hd.2.1, hd.2.2.1, hf.1, ?_, ?_⟩
    · rw [hf.2.2.2, if_pos hd.2.2.2.le]
    · have he := actual_gap κ K t hκ hκ1 hK hd.1 hd.2.1 hd.2.2.1
      have hp := mul_pos hd.1 hg
      linarith

private def symmetricGap (a b c : ℝ) : ℝ :=
  2 * b ^ 2 / (3 * Real.sqrt (a * (1 - a))) -
    8 * b ^ 2 / (3 * Real.sqrt ((2 * a + c) * (3 - 2 * a - c))) -
    4 * (c - a) ^ 2 / (3 * ((2 * a + c) * (3 - 2 * a - c)))

private theorem symmetricGap_actual (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (hc1 : c < 1) :
    symmetricGap a b c = (pgmScore (rho a b c) {0, 1} - 1 / 3) -
      2 * (pgmScore (rho a b c) Finset.univ - 1 / 3) := by
  rw [(D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison.symmetric_scores a b c ha ha1 hc hc1).1,
    (D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison.symmetric_scores a b c ha ha1 hc hc1).2]
  dsimp [symmetricGap]
  ring

open Filter Topology in
/-- Every strict certified violating point is stable under all sufficiently
small symmetric-model perturbations. The assertion includes actual PD states,
strict inactivity, actual unique optimum, and the strict actual CFC gap. -/
theorem strict_stability (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hc : 0 < c) (hc1 : c < 1)
    (hd : 0 < a * (1 - a) - b ^ 2) (hactive : |c - a| < b)
    (hgap : 2 * (pgmScore (rho a b c) Finset.univ - 1 / 3) <
      pgmScore (rho a b c) {0, 1} - 1 / 3) :
    ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 (a, b, c),
      (∀ i, (rho p.1 p.2.1 p.2.2 i).PosDef ∧ trace (rho p.1 p.2.1 p.2.2 i) = 1) ∧
      0 < p.2.1 ∧ |p.2.2 - p.1| < p.2.1 ∧ finitePOVM pairPovm ∧
      (∀ E, finitePOVM E →
        ((∀ F, finitePOVM F → success (rho p.1 p.2.1 p.2.2) F ≤
          success (rho p.1 p.2.1 p.2.2) E) ↔ E = pairPovm)) ∧
      2 * (pgmScore (rho p.1 p.2.1 p.2.2) Finset.univ - 1 / 3) <
        pgmScore (rho p.1 p.2.1 p.2.2) {0, 1} - 1 / 3 := by
  have ca : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1) (a, b, c) := by fun_prop
  have cb : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.1) (a, b, c) := by fun_prop
  have cc : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.2) (a, b, c) := by fun_prop
  have cd : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1 * (1 - p.1) - p.2.1 ^ 2)
      (a, b, c) := by fun_prop
  have ci : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.1 - |p.2.2 - p.1|)
      (a, b, c) := by fun_prop
  have hq : 0 < a * (1 - a) := mul_pos ha (sub_pos.mpr ha1)
  have hD : 0 < (2 * a + c) * (3 - 2 * a - c) := mul_pos (by positivity) (by linarith)
  have cg : ContinuousAt (fun p : ℝ × ℝ × ℝ => symmetricGap p.1 p.2.1 p.2.2)
      (a, b, c) := by
    dsimp [symmetricGap]
    fun_prop (disch := positivity)
  have hg : 0 < symmetricGap a b c := by
    rw [symmetricGap_actual a b c ha ha1 hc hc1]
    linarith
  filter_upwards [ca.tendsto.eventually_const_lt ha, ca.tendsto.eventually_lt_const ha1,
    cb.tendsto.eventually_const_lt hb, cc.tendsto.eventually_const_lt hc,
    cc.tendsto.eventually_lt_const hc1, cd.tendsto.eventually_const_lt hd,
    ci.tendsto.eventually_const_lt (sub_pos.mpr hactive),
    cg.tendsto.eventually_const_lt hg] with p hpa hpa1 hpb hpc hpc1 hpd hpi hpg
  have hpi' : |p.2.2 - p.1| < p.2.1 := by linarith
  have hopt := pair_classification p.1 p.2.1 p.2.2 hpb hpi'.le
  refine ⟨states_posDef _ _ _ hpa hpc hpc1 hpd, hpb, hpi', hopt.1, hopt.2.2, ?_⟩
  rw [symmetricGap_actual p.1 p.2.1 p.2.2 hpa hpa1 hpc hpc1] at hpg
  linarith

open Filter Topology Asymptotics in
/-- The complete loading expansion with an actual-score cubic remainder. -/
theorem asymptotics (κ K : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) (hK : 1 < K) :
    (fun t : ℝ => (pgmScore (states κ K t) {0, 1} - 1 / 3) -
      2 * (pgmScore (states κ K t) Finset.univ - 1 / 3) -
      (2 * κ ^ 2 / 3) * (1 - 4 / Real.sqrt (3 * (K + 2))) * t +
      (4 * (K - 1) ^ 2 / (9 * (K + 2))) * t ^ 2)
      =O[𝓝[>] 0] (fun t => t ^ 3) := by
  let L := K + 2
  let v : ℝ → ℝ := fun t => 1 - L * t ^ 2 / 3
  let B := 4 * (K - 1) ^ 2 / (9 * L)
  let r : ℝ → ℝ := fun t =>
    2 * κ ^ 2 / (3 * Real.sqrt (1 - t ^ 2) * (1 + Real.sqrt (1 - t ^ 2))) -
      (8 * κ ^ 2 / (3 * Real.sqrt (3 * L))) * (L / 3) /
        (Real.sqrt (v t) * (1 + Real.sqrt (v t))) -
      B * (L / 3) * t / v t
  have hL : 0 < L := by dsimp [L]; linarith
  have hc : ContinuousAt r 0 := by
    dsimp [r, v]
    fun_prop (disch := norm_num <;> positivity)
  have hO : (fun t : ℝ => t ^ 3 * r t) =O[𝓝[>] 0] (fun t => t ^ 3) := by
    simpa only [mul_one] using (isBigO_refl (fun t : ℝ => t ^ 3) (𝓝[>] 0)).mul
      ((hc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ)
  apply hO.congr' ?_ EventuallyEq.rfl
  filter_upwards [small_loading κ K hκ hκ1 hK] with t ht
  rw [actual_gap κ K t hκ hκ1 hK ht.1 ht.2.1 ht.2.2.1]
  obtain ⟨ha, ha1, hca, hc1, hd⟩ := domain κ K t hκ hκ1 hK ht.1 ht.2.1 ht.2.2.1
  have hv : 0 < v t := by
    dsimp [v, L]
    nlinarith
  have hF : (K + 2) * (3 - (K + 2) * t ^ 2) = (3 * L) * v t := by
    dsimp [L, v]; ring
  have hFroot : Real.sqrt ((K + 2) * (3 - (K + 2) * t ^ 2)) =
      Real.sqrt (3 * L) * Real.sqrt (v t) := by
    rw [hF, Real.sqrt_mul (by positivity)]
  have hRa := D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison.inverse_sqrt_residual (t ^ 2) ha
  have hRv := D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmComparison.inverse_sqrt_residual
    (L * t ^ 2 / 3) hv
  have hlin : 1 / v t - 1 = (L * t ^ 2 / 3) / v t := by
    have hn : 3 - L * t ^ 2 ≠ 0 := by dsimp [v] at hv; nlinarith
    dsimp [v]
    field_simp [hn] <;> ring
  have he : t ^ 3 * r t =
      (2 * κ ^ 2 / 3) * t * (1 / Real.sqrt (1 - t ^ 2) - 1) -
      (8 * κ ^ 2 / (3 * Real.sqrt (3 * L))) * t * (1 / Real.sqrt (v t) - 1) -
      B * t ^ 2 * (1 / v t - 1) := by
    rw [hRa, hRv, hlin]
    dsimp [r, v]
    field_simp <;> ring
  rw [he]
  dsimp [scaledGap]
  rw [hFroot]
  have hden : (K + 2) * (3 - (K + 2) * t ^ 2) = 3 * L * v t := hF
  dsimp [B, L, v] at *
  field_simp <;> ring


end D5.S3.Quantum.Measurement.Pgm.EquiprobablePgmLoading

/- Escape-audit delivery: four source-bound registrations are currently validated
for SupportIdentity.centered_identity/random_guessing_le and
Symmetric.states_posDef/pair_classification. The remaining theorem-specific
bindings are unfinished and disclosed at
https://github.com/the-omega-institute/trureturing/issues/27499.
That issue is not proof, registration validation or independent approval. -/
