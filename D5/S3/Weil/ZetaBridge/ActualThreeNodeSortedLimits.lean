/- GID: D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: Sorted limits of the actual infinite three-node tail Gram follow in both branches from the full336 multiplicative squeeze. -/

import D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteLimits
import D5.S3.Weil.ZetaBridge.ActualThreeNodeFull336
import D5.S3.Quantum.Schatten.SingularValueOrder

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder Matrix Topology
open D5.S3.Weil.ZetaBridge
open Filter Set
open ActualThreeNodeSourceHeadBridge ActualThreeNodeFiniteAlgebra ActualThreeNodeFiniteEnergy
open ActualThreeNodeFiniteSpectrum ActualThreeNodeFiniteLimits ActualThreeNodeFull336
open PrimeSymbolResonance WeilArithmeticCouplingJet WeilArithmeticCouplingParityGram
open D5.S3.Quantum.Schatten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeSortedLimits

lemma actual_mean_nonneg {c : ℕ} (hc : 3 ≤ c) : 0 ≤ mean c :=
  (by positivity : (0 : ℝ) ≤ (Real.log (2 : ℝ)) ^ 2 / 4).trans
    (prime_symbol_mean_lower_bound hc)

lemma actual_h_pos {c : ℕ} (hc : 3 ≤ c) : 0 < (Real.pi / 4) ^ 2 + mean c := by
  have hg : 0 < Real.pi / 4 := div_pos Real.pi_pos (by norm_num)
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hg) (actual_mean_nonneg hc)

lemma actual_gmu_pos {c : ℕ} (hc : 3 ≤ c) : 0 < (Real.pi / 4) ^ 2 + 4 * mean c := by
  have hh := actual_h_pos hc
  have hm := actual_mean_nonneg hc
  linarith

/-- The small-root constants are strictly positive in BOTH actual branches. -/
lemma actual_last_constants_pos {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0) :
    0 < 16 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 4 / (135 * Real.pi ^ 2) ∧
    (arithmeticBoundarySymbol c n ≠ 0 →
      0 < (n : ℝ) ^ 2 * (arithmeticBoundarySymbol c n) ^ 2 *
        ((Real.pi / 4) ^ 2 + 4 * mean c) /
        (9 * Real.pi ^ 2 * ((Real.pi / 4) ^ 2 + mean c))) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero hnR
  have hn4 : 0 < (n : ℝ) ^ 4 := by
    simpa only [← pow_mul] using pow_pos hn2 2
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hh := actual_h_pos hc
  have hgmu := actual_gmu_pos hc
  constructor
  · positivity
  · intro ha
    have ha2 : 0 < (arithmeticBoundarySymbol c n) ^ 2 := sq_pos_of_ne_zero ha
    positivity

/-- Genuine eventual positive small root for the actual nonzero arithmetic branch.
No arithmetic nonvanishing claim is used; this theorem has the explicit branch hypothesis. -/
lemma actual_nonzero_eventual_roots_pos {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)
    (ha : arithmeticBoundarySymbol c n ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      0 < rhoPlus (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) ∧
      0 < O (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) ∧
      0 < rhoMinus (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) := by
  have hh := actual_h_pos hc
  have hgmu := actual_gmu_pos hc
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero hnR
  have ha2 : 0 < (arithmeticBoundarySymbol c n) ^ 2 := sq_pos_of_ne_zero ha
  have hl : 0 < (n : ℝ) ^ 2 * (arithmeticBoundarySymbol c n) ^ 2 *
      ((Real.pi / 4) ^ 2 + 4 * mean c) / (9 * ((Real.pi / 4) ^ 2 + mean c)) := by positivity
  rcases root_limits (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) n hh with ⟨hp, hm, ho⟩
  have hlarge : 0 < 6 * ((Real.pi / 4) ^ 2 + mean c) := by positivity
  have hodd : 0 < 4 * (arithmeticBoundarySymbol c n) ^ 2 := by positivity
  have hsmall := scaled_small_root_limit (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) n hh
  filter_upwards [hp.eventually (Ioi_mem_nhds hlarge), ho.eventually (Ioi_mem_nhds hodd),
    hsmall.eventually (Ioi_mem_nhds hl)] with N hpN hoN hmN
  refine ⟨hpN, hoN, ?_⟩
  by_contra h
  have hle : rhoMinus (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) ≤ 0 :=
    le_of_not_gt h
  have hmul := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (N : ℝ)) hle
  exact (not_lt_of_ge hmul) hmN

/-- Relative factors converge without any arithmetic branch or vector parameter. -/
theorem relative_factor_limits (c : ℕ) (n : ℤ) :
    Tendsto (lower336 c) atTop (𝓝 1) ∧
      Tendsto (fun N : ℕ => upper336 c N n) atTop (𝓝 1) := by
  have hd := tendsto_const_div_atTop_nhds_zero_nat (delta336 c)
  have hr := tendsto_const_div_atTop_nhds_zero_nat (n : ℝ)
  constructor
  · change Tendsto (fun N : ℕ => 1 - delta336 c / (N : ℝ)) atTop (𝓝 1)
    simpa only [Pi.sub_apply, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hd
  · have hnum := (tendsto_const_nhds (x := (1 : ℝ))).add hd
    have hden := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hr.pow 2)).pow 2
    have hu := (hnum.div hden (by norm_num : (1 - (0 : ℝ) ^ 2) ^ 2 ≠ 0)).congr
      (f₂ := fun N : ℕ => upper336 c N n) (fun N => rfl)
    simpa using hu

/-- One eventual cutoff precedes every vector and every sorted eigenvalue index.
Strict positivity is stronger than the nonnegativity required by the scaling API. -/
theorem actual_admissible_cutoff (c : ℕ) (n : ℤ) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      9 ≤ N ∧ |(n : ℝ)| < (N : ℝ) ∧ delta336 c < (N : ℝ) ∧
        0 < lower336 c N ∧ 0 < upper336 c N n := by
  rcases relative_factor_limits c n with ⟨hl, hu⟩
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (9 : ℕ), exterior_eventually n,
      hl.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hu.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN hR hlN huN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdiv : delta336 c / (N : ℝ) < 1 := by
    dsimp only [lower336] at hlN
    linarith
  exact ⟨hN, hR.2, (div_lt_one hNr).mp hdiv, hlN, huN⟩

/-- The actual Gram eigenvalues, in the inherited ORIGINAL orthonormal head metric. -/
abbrev actualEigen {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) : Fin 3 → ℝ :=
  (show (actualTailGram hc n N).IsHermitian from Matrix.isHermitian_gram _ _).eigenvalues₀

/-- Direct uses of the EXISTING sorted eigenvalue APIs on the ACTUAL comparison.
This is not a replacement minmax theorem and does not accept a supplied form. -/
theorem actual_sorted_relative_bounds {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)
    (N : ℕ) (hN9 : 9 ≤ N) (hR : |(n : ℝ)| < (N : ℝ))
    (hl : 0 ≤ lower336 c N) (hu : 0 ≤ upper336 c N n) (i : Fin 3) :
    lower336 c N * finiteEigen (Real.pi / 4) (mean c)
        (arithmeticBoundarySymbol c n) ((n : ℝ) / N) i ≤
      (Real.pi ^ 2 * N) * actualEigen hc n N i ∧
    (Real.pi ^ 2 * N) * actualEigen hc n N i ≤
      upper336 c N n * finiteEigen (Real.pi / 4) (mean c)
        (arithmeticBoundarySymbol c n) ((n : ℝ) / N) i := by
  let H := finiteMatrix (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N)
  let K := actualTailGram hc n N
  have hH : H.IsHermitian := finiteMatrix_isHermitian _ _ _ _
  have hK : K.IsHermitian := Matrix.isHermitian_gram _ _
  have hreal (q : ℝ) : IsSelfAdjoint (q : ℂ) := by
    change star (q : ℂ) = (q : ℂ)
    simp
  have hLH := hH.smul (hreal (lower336 c N))
  have hUH := hH.smul (hreal (upper336 c N n))
  have hSK := hK.smul (hreal (Real.pi ^ 2 * N))
  have hq : 0 ≤ Real.pi ^ 2 * (N : ℝ) := mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hcmp := actual_full336_loewner hc hn N hN9 hR
  change ((((Real.pi ^ 2 * N : ℝ) : ℂ) • K) - ((lower336 c N : ℂ) • H)).PosSemidef ∧
    (((upper336 c N n : ℂ) • H) - (((Real.pi ^ 2 * N : ℝ) : ℂ) • K)).PosSemidef at hcmp
  have hlo := eigenvalues_zero_mono hLH hSK hcmp.1 i
  have hup := eigenvalues_zero_mono hSK hUH hcmp.2 i
  rw [eigenvalues_zero_smul H hH _ hl hLH i,
      eigenvalues_zero_smul K hK _ hq hSK i] at hlo
  rw [eigenvalues_zero_smul K hK _ hq hSK i,
      eigenvalues_zero_smul H hH _ hu hUH i] at hup
  exact ⟨hlo, hup⟩

/-- Scalar squeeze for THIS actual Gram, consumed six times below.
The only input limit is a concrete finite H_N eigenvalue limit; all matrix and
infinite-tail comparison hypotheses are proved internally from the source. -/
private theorem actual_scaled_limit {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)
    (i : Fin 3) (e : ℕ) (L : ℝ)
    (hfinite : Tendsto (fun N : ℕ => (N : ℝ) ^ e *
      finiteEigen (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) i)
      atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (e + 1) * actualEigen hc n N i) atTop (𝓝 (L / Real.pi ^ 2)) := by
  rcases relative_factor_limits c n with ⟨hl, hu⟩
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hlo := (hl.mul hfinite).div_const (Real.pi ^ 2)
  have hup := (hu.mul hfinite).div_const (Real.pi ^ 2)
  simp only [one_mul] at hlo hup
  obtain ⟨N0, hcut⟩ := actual_admissible_cutoff c n
  have hb : ∀ᶠ N : ℕ in atTop,
      (lower336 c N * ((N : ℝ) ^ e * finiteEigen (Real.pi / 4) (mean c)
        (arithmeticBoundarySymbol c n) ((n : ℝ) / N) i)) / Real.pi ^ 2 ≤
          (N : ℝ) ^ (e + 1) * actualEigen hc n N i ∧
      (N : ℝ) ^ (e + 1) * actualEigen hc n N i ≤
        (upper336 c N n * ((N : ℝ) ^ e * finiteEigen (Real.pi / 4) (mean c)
          (arithmeticBoundarySymbol c n) ((n : ℝ) / N) i)) / Real.pi ^ 2 := by
    filter_upwards [eventually_ge_atTop N0] with N hN0
    rcases hcut N hN0 with ⟨hN9, hR, _hdelta, hlN, huN⟩
    have hcmp := actual_sorted_relative_bounds hc hn N hN9 hR hlN.le huN.le i
    have hm : 0 ≤ (N : ℝ) ^ e / Real.pi ^ 2 :=
      div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hp.le
    have h1 := mul_le_mul_of_nonneg_left hcmp.1 hm
    have h2 := mul_le_mul_of_nonneg_left hcmp.2 hm
    have hmid : ((N : ℝ) ^ e / Real.pi ^ 2) *
        ((Real.pi ^ 2 * N) * actualEigen hc n N i) =
        (N : ℝ) ^ (e + 1) * actualEigen hc n N i := by
      rw [pow_succ]
      field_simp [hp.ne']
      <;> ring
    rw [hmid] at h1 h2
    constructor
    · convert h1 using 1 <;> ring
    · convert h2 using 1 <;> ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup (hb.mono fun N hN => hN.1)
    (hb.mono fun N hN => hN.2)

/-- Final nonzero-symbol limits of the GENUINE infinite-tail Gram in the
original coefficient norm. Ties survive as max/min. Every signed n != 0. -/
theorem actual_nonzero_sorted_limits {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)
    (ha : arithmeticBoundarySymbol c n ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℝ) * actualEigen hc n N 0) atTop
      (𝓝 (max (6 * ((Real.pi / 4) ^ 2 + mean c))
        (4 * (arithmeticBoundarySymbol c n) ^ 2) / Real.pi ^ 2)) ∧
    Tendsto (fun N : ℕ => (N : ℝ) * actualEigen hc n N 1) atTop
      (𝓝 (min (6 * ((Real.pi / 4) ^ 2 + mean c))
        (4 * (arithmeticBoundarySymbol c n) ^ 2) / Real.pi ^ 2)) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ 3 * actualEigen hc n N 2) atTop
      (𝓝 ((n : ℝ) ^ 2 * (arithmeticBoundarySymbol c n) ^ 2 *
        ((Real.pi / 4) ^ 2 + 4 * mean c) /
        (9 * Real.pi ^ 2 * ((Real.pi / 4) ^ 2 + mean c)))) ∧
    0 < (n : ℝ) ^ 2 * (arithmeticBoundarySymbol c n) ^ 2 *
        ((Real.pi / 4) ^ 2 + 4 * mean c) /
        (9 * Real.pi ^ 2 * ((Real.pi / 4) ^ 2 + mean c)) := by
  have hh := actual_h_pos hc
  have hf := finite_nonzero_limits (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) n hh ha
  have hp : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  refine ⟨?_, ?_, ?_, (actual_last_constants_pos hc hn).2 ha⟩
  · have h0 : Tendsto (fun N : ℕ => (N : ℝ) ^ 0 *
        finiteEigen (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) 0)
        atTop (𝓝 (max (6 * ((Real.pi / 4) ^ 2 + mean c)) (4 * (arithmeticBoundarySymbol c n) ^ 2))) := by
      simpa only [pow_zero, one_mul] using hf.1
    simpa only [Nat.zero_add, pow_one] using actual_scaled_limit hc hn 0 0 _ h0
  · have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ 0 *
        finiteEigen (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) 1)
        atTop (𝓝 (min (6 * ((Real.pi / 4) ^ 2 + mean c)) (4 * (arithmeticBoundarySymbol c n) ^ 2))) := by
      simpa only [pow_zero, one_mul] using hf.2.1
    simpa only [Nat.zero_add, pow_one] using actual_scaled_limit hc hn 1 0 _ h1
  · have hs := actual_scaled_limit hc hn 2 2 _ hf.2.2
    have hconst : ((n : ℝ) ^ 2 * (arithmeticBoundarySymbol c n) ^ 2 *
        ((Real.pi / 4) ^ 2 + 4 * mean c) / (9 * ((Real.pi / 4) ^ 2 + mean c))) / Real.pi ^ 2 =
        (n : ℝ) ^ 2 * (arithmeticBoundarySymbol c n) ^ 2 *
          ((Real.pi / 4) ^ 2 + 4 * mean c) /
          (9 * Real.pi ^ 2 * ((Real.pi / 4) ^ 2 + mean c)) := by
      field_simp [hp, hh.ne']
      <;> ring
    simpa only [hconst] using hs

/-- Final ZERO-symbol limits. No nonvanishing assumption is silently introduced.
The scales are N,N^3,N^5 and the last constant is strictly positive. -/
theorem actual_zero_sorted_limits {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)
    (ha : arithmeticBoundarySymbol c n = 0) :
    Tendsto (fun N : ℕ => (N : ℝ) * actualEigen hc n N 0) atTop
      (𝓝 (6 * ((Real.pi / 4) ^ 2 + mean c) / Real.pi ^ 2)) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ 3 * actualEigen hc n N 1) atTop
      (𝓝 (4 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 2 / (3 * Real.pi ^ 2))) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ 5 * actualEigen hc n N 2) atTop
      (𝓝 (16 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 4 / (135 * Real.pi ^ 2))) ∧
    0 < 16 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 4 / (135 * Real.pi ^ 2) := by
  have hh := actual_h_pos hc
  have hf := finite_zero_limits (Real.pi / 4) (mean c) hn hh
  have hp : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  refine ⟨?_, ?_, ?_, (actual_last_constants_pos hc hn).1⟩
  · have h0 : Tendsto (fun N : ℕ => (N : ℝ) ^ 0 *
        finiteEigen (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) 0)
        atTop (𝓝 (6 * ((Real.pi / 4) ^ 2 + mean c))) := by
      simpa only [ha, pow_zero, one_mul] using hf.1
    simpa only [Nat.zero_add, pow_one] using actual_scaled_limit hc hn 0 0 _ h0
  · have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 *
        finiteEigen (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) 1)
        atTop (𝓝 (4 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 2 / 3)) := by
      simpa only [ha] using hf.2.1
    have hs := actual_scaled_limit hc hn 1 2 _ h1
    have hconst : (4 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 2 / 3) / Real.pi ^ 2 =
        4 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 2 / (3 * Real.pi ^ 2) := by
      field_simp [hp]
      <;> ring
    simpa only [hconst] using hs
  · have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ 4 *
        finiteEigen (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) 2)
        atTop (𝓝 (16 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 4 / 135)) := by
      simpa only [ha] using hf.2.2
    have hs := actual_scaled_limit hc hn 2 4 _ h2
    have hconst : (16 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 4 / 135) / Real.pi ^ 2 =
        16 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 4 / (135 * Real.pi ^ 2) := by
      field_simp [hp]
      <;> ring
    simpa only [hconst] using hs

end D5.S3.Weil.ZetaBridge.ActualThreeNodeSortedLimits
