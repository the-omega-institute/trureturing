/- GID: D5/S3/Quantum/Foundation/TwoRoundOptimalAsymptotics
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/TwoRoundOptimalAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform next-order optimal value and all original optimizer marginal asymptotics. -/
import D5.S3.Quantum.Foundation.TwoRoundRankOneReduction

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
namespace D5.S3.Quantum.Foundation.TwoRoundOptimalAsymptotics
open D5.S3.Quantum.Foundation.TwoRoundPhaseAverage
open D5.S3.Quantum.Foundation.TwoRoundSpectralEvents
open D5.S3.Quantum.Foundation.TwoRoundRankOneReduction
open D5.S3.Quantum.Information.PartialTraceMutualInformation

private theorem arrow_root_bound (k r a q t : ℝ)
    (hk : 0 ≤ k) (hk1 : k ≤ 1 / 2) (hr : 0 ≤ r) (hra : r ≤ a) (hr1 : r ≤ 1)
    (ha : 0 ≤ a) (haeq : a * (1 + 2 * k) = k ^ 2)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (q + Real.sqrt (q ^ 2 + 4 * k ^ 2 * q * (1 - q) + 4 * r * q * t)) / 2 +
      max (1 - q - t) 0 ≤ 1 + a := by
  let A := q ^ 2 + 4 * k ^ 2 * q * (1 - q) + 4 * r * q * t
  have hqt : q * t ≤ 1 := (mul_le_mul hq1 ht1 ht (by norm_num)).trans_eq (by norm_num)
  have hkk : 0 ≤ 1 - 4 * k ^ 2 := by nlinarith
  have hA : A ≤ 1 + 4 * r := by
    dsimp [A]
    nlinarith [mul_nonneg hkk (mul_nonneg hq (sub_nonneg.mpr hq1)),
      mul_nonneg hr (sub_nonneg.mpr hqt)]
  have hp : Real.sqrt A ≤ 1 + 2 * r := Real.sqrt_le_iff.mpr
    ⟨by linarith, by nlinarith [sq_nonneg r]⟩
  have hcert : (q + 2 * a + 2 * t) ^ 2 - A =
      4 * (k * q - a) ^ 2 + 4 * (1 - r) * q * t + 8 * a * t + 4 * t ^ 2 := by
    dsimp [A]
    linear_combination 4 * q * haeq
  have hn : Real.sqrt A ≤ q + 2 * a + 2 * t := Real.sqrt_le_iff.mpr
    ⟨by positivity, by
      nlinarith [sq_nonneg (k * q - a),
        mul_nonneg (mul_nonneg (sub_nonneg.mpr hr1) hq) ht, mul_nonneg ha ht,
        sq_nonneg t]⟩
  change (q + Real.sqrt A) / 2 + max (1 - q - t) 0 ≤ _
  rw [add_max]
  exact max_le (by linarith) (by linarith)

def explicitValue (eps : ℝ) : ℝ :=
  eps * (1 + (Real.sqrt (1 - eps)) ^ 2 /
    ((1 + Real.sqrt (1 - eps)) * (1 + 3 * Real.sqrt (1 - eps))))

private theorem explicit_scalar_upper (eps : ℝ) (he : 0 < eps) (he16 : eps ≤ 1 / 16) :
    (∀ q t : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ t → t ≤ 1 →
      scalarLambda eps eps q t + max (eps * (1 - q - t)) 0 ≤ explicitValue eps) ∧
      explicitValue eps < 9 * eps / 8 := by
  let c := Real.sqrt (1 - eps)
  let k := c / (1 + c)
  let r := eps / (1 + c) ^ 2
  let a := k ^ 2 / (1 + 2 * k)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcs : c ^ 2 = 1 - eps := Real.sq_sqrt (by linarith)
  have hc : 15 / 16 < c := by nlinarith
  have hc1 : c < 1 := by nlinarith
  have hcden : 0 < 1 + c := by linarith
  have hk0 : 0 ≤ k := div_nonneg hc0 hcden.le
  have hklo : 2 / 5 ≤ k := (le_div_iff₀ hcden).mpr (by linarith)
  have hk1 : k < 1 / 2 := (div_lt_iff₀ hcden).mpr (by linarith)
  have hkden : 0 < 1 + 2 * k := by linarith
  have hr0 : 0 ≤ r := div_nonneg he.le (sq_nonneg _)
  have hr16 : r ≤ 1 / 16 := (div_le_iff₀ (pow_pos hcden 2)).mpr (by nlinarith)
  have ha0 : 0 ≤ a := div_nonneg (sq_nonneg _) hkden.le
  have halo : 1 / 16 ≤ a := (le_div_iff₀ hkden).mpr (by nlinarith)
  have ha1 : a < 1 / 8 := (div_lt_iff₀ hkden).mpr (by
    nlinarith [mul_pos (show 0 < 1 / 2 - k by linarith) (show 0 < k + 1 / 4 by linarith)])
  have haeq : a * (1 + 2 * k) = k ^ 2 := div_mul_cancel₀ _ hkden.ne'
  have hd : explicitValue eps = eps * (1 + a) := by
    dsimp [explicitValue, a, k, c]
    field_simp
    ring
  refine ⟨?_, by rw [hd]; nlinarith [mul_pos he (sub_pos.mpr ha1)]⟩
  intro q t hq hq1 ht ht1
  let A := q ^ 2 + 4 * k ^ 2 * q * (1 - q) + 4 * r * q * t
  have hdisc : (scalarU eps q t + scalarV eps t) ^ 2 -
      4 * scalarW eps eps q t ^ 2 = eps ^ 2 * A := by
    simp only [scalarU, scalarV, scalarW, Real.sqrt_mul_self he.le]
    change (q + (1 - eps) * (1 - q) + eps * t + (1 - eps + eps * t)) ^ 2 -
      4 * (c * (q + c * (1 - q)) + eps * t) ^ 2 = eps ^ 2 * A
    dsimp [A, k, r]
    have heq : eps = 1 - c ^ 2 := by linarith
    rw [heq]
    field_simp [hcden.ne']
    ring
  have hl : scalarLambda eps eps q t = eps * ((q + Real.sqrt A) / 2) := by
    rw [scalarLambda, hdisc, Real.sqrt_mul (sq_nonneg eps), Real.sqrt_sq he.le]
    dsimp [scalarU, scalarV]
    ring
  have hb := arrow_root_bound k r a q t hk0 hk1.le hr0 (hr16.trans halo)
    (by linarith) ha0 haeq hq hq1 ht ht1
  rw [hl, hd]
  have hmax : max (eps * (1 - q - t)) 0 = eps * max (1 - q - t) 0 := by
    rw [mul_max_of_nonneg _ _ he.le, mul_zero]
  rw [hmax, ← mul_add]
  exact mul_le_mul_of_nonneg_left hb he.le

/-- The explicit repair bounds the infimum over all original complex causal pairs. -/
theorem explicit_repair_upper (eps : ℝ) (he : 0 < eps) (he16 : eps ≤ 1 / 16) :
    optimalError eps ≤ explicitValue eps ∧ explicitValue eps < 9 * eps / 8 := by
  have he1 : eps ≤ 1 := by linarith
  obtain ⟨hs, hd⟩ := explicit_scalar_upper eps he he16
  have hn := tester_norm_le ((rank_one_full_objective eps eps (explicitValue eps)
    he.le he1 he.le he1).mpr hs)
  obtain ⟨h0, h1, h2⟩ := rankOneBlock_budgets eps he.le he1
  have hR := (compressed_block_causal_lift eps (rankOneBlock eps) he.le he1
    (rankOneBlock_pos eps) h0.le h1.le h2.le).1
  obtain ⟨_, _, _, _, hmin⟩ := original_minimum_attained eps
  exact ⟨(hmin _ _ hR).trans hn, hd⟩

private def xyEffect (q : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (q * (1 - q) : ℝ) • vecMulVec ![(1 : ℂ), 1, 0] (star ![(1 : ℂ), 1, 0])

private theorem xyEffect_apply (q : ℝ) (i j : Fin 3) :
    xyEffect q i j = (q * (1 - q) : ℝ) •
      (![(1 : ℂ), 1, 0] i * star (![(1 : ℂ), 1, 0] j)) := rfl

private theorem xy_effect_interval (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    EventInterval (compressedNormalization q 0) (xyEffect q) := by
  refine ⟨(posSemidef_vecMulVec_self_star _).smul (mul_nonneg hq (sub_nonneg.mpr hq1)), ?_⟩
  have hs : compressedNormalization q 0 - xyEffect q =
      vecMulVec ![(q : ℂ), ((q - 1 : ℝ) : ℂ), 0]
        (star ![(q : ℂ), ((q - 1 : ℝ) : ℂ), 0]) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [compressedNormalization, xyEffect_apply, Matrix.diagonal, Matrix.smul_apply, Pi.smul_apply, Pi.star_apply,
        Complex.real_smul, vecMulVec_apply] <;> ring
  rw [hs]
  exact posSemidef_vecMulVec_self_star _

private theorem xy_pairing (X : Matrix Wire Wire ℂ) (hX : X.IsHermitian) (q : ℝ) :
    eventResponse X (embedBlock (xyEffect q)) = q * (1 - q) *
      ((X (mainAddress 0) (mainAddress 0)).re + (X (mainAddress 1) (mainAddress 1)).re +
        2 * (X (mainAddress 0) (mainAddress 1)).re) := by
  have hs := congrArg Complex.re (hX.apply (mainAddress 0) (mainAddress 1))
  simp only [Complex.star_def, Complex.conj_re] at hs
  rw [response_compressed_event]
  simp [eventResponse, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three, xyEffect_apply,
    Matrix.smul_apply, Pi.smul_apply, Pi.star_apply, Complex.real_smul, vecMulVec_apply, Complex.mul_re]
  rw [hs]
  ring

/-- A full normalization-minus-event test bounds every original complex causal repair. -/
theorem raw_full_block_dual_barrier (eps : ℝ) (S : Matrix Wire Wire ℂ)
    (sigma : Matrix (Fin 2) (Fin 2) ℂ) (he : 0 ≤ eps) (he1 : eps ≤ 1)
    (hS : Causal S sigma) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    eps * (1 - q) + q * (1 - q) *
      ((1 + Real.sqrt (1 - eps)) ^ 2 - 4 * (1 - (sigma 1 1).re)) ≤
        testerNorm (candidate eps - S) := by
  let p := (sigma 1 1).re
  let P := S.submatrix mainAddress mainAddress
  let C := diagonalTester q 0
  let M := testerNormalization q 0
  let L := embedBlock (xyEffect q)
  obtain ⟨hp, hp1, hP, h0, h1, h2⟩ := causal_principal_block_budgets S sigma hS
  have hqq : 0 ≤ q * (1 - q) := mul_nonneg hq (sub_nonneg.mpr hq1)
  have hxy : (P 0 1).re ≤ 1 - p := by
    have hs := D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.psd_entry_bound hP 0 1
    have hm := mul_le_mul h0 h1 (Complex.nonneg_iff.mp (hP.diag_nonneg (i := 1))).1
      (sub_nonneg.mpr hp1)
    simp only [Complex.normSq_apply] at hs
    nlinarith [sq_nonneg (P 0 1).im]
  have hSL : eventResponse S L ≤ 4 * q * (1 - q) * (1 - p) := by
    rw [show L = embedBlock (xyEffect q) from rfl, xy_pairing S hS.1.isHermitian]
    have hb : (P 0 0).re + (P 1 1).re + 2 * (P 0 1).re ≤ 4 * (1 - p) := by linarith
    have hm := mul_le_mul_of_nonneg_left hb hqq
    dsimp [P] at hm
    nlinarith
  have hRL : eventResponse (candidate eps) L =
      q * (1 - q) * (1 + Real.sqrt (1 - eps)) ^ 2 := by
    rw [show L = embedBlock (xyEffect q) from rfl,
      xy_pairing (candidate eps)
        (show (candidate eps).IsHermitian from
          (posSemidef_vecMulVec_self_star (candidateVector eps)).isHermitian)]
    simp [candidate, candidateVector, mainAddress, vecMulVec_apply]
    ring_nf
    simp
  have hC := diagonalTester_pos q 0 hq hq1 (by norm_num) (by norm_num)
  have hCn := diagonalTester_normalized q 0
  have hL := lift_compressed_event q 0 hq hq1 (by norm_num) (by norm_num)
    (xy_effect_interval q hq hq1)
  have hT : Tester C (M - L) := ⟨hC, hCn, hL.2, by
    change (M - (M - L)).PosSemidef
    simpa only [sub_sub_cancel] using hL.1⟩
  have hSM : eventResponse S M = 1 := by
    unfold eventResponse
    rw [show M = C ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ) from rfl,
      normalization_trace S sigma C hS.2.2.2 hS.2.2.1 hCn]
    simp
  have hRM := candidate_normalization_response eps q 0 he he1
  have hv : response (candidate eps - S) (M - L) =
      -eps * (1 - q) - q * (1 - q) * (1 + Real.sqrt (1 - eps)) ^ 2 +
        eventResponse S L := by
    simp only [response, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    change eventResponse (candidate eps) M - eventResponse S M -
      (eventResponse (candidate eps) L - eventResponse S L) = _
    rw [hSM, hRL, hRM]
    ring
  obtain ⟨_, _, _, _, hb⟩ := tester_norm_attained (candidate eps - S)
  have h := (neg_le_abs (response (candidate eps - S) (M - L))).trans (hb C (M - L) hT)
  rw [hv] at h
  dsimp [p] at hSL
  nlinarith

private def xzEffect (s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 2 : ℝ) • vecMulVec ![(1 : ℂ), 0, (s : ℂ)] (star ![(1 : ℂ), 0, (s : ℂ)])

private theorem xzEffect_apply (s : ℝ) (i j : Fin 3) :
    xzEffect s i j = (1 / 2 : ℝ) •
      (![(1 : ℂ), 0, (s : ℂ)] i * star (![(1 : ℂ), 0, (s : ℂ)] j)) := rfl

private theorem xz_effect_intervals :
    EventInterval (compressedNormalization 1 1) (xzEffect 1) ∧
      EventInterval (compressedNormalization 1 1) (xzEffect (-1)) := by
  have hp (s : ℝ) : (xzEffect s).PosSemidef :=
    (posSemidef_vecMulVec_self_star _).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have heq : compressedNormalization 1 1 - xzEffect 1 = xzEffect (-1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [compressedNormalization, xzEffect_apply, Matrix.diagonal, Matrix.smul_apply, Pi.smul_apply, Pi.star_apply,
        Complex.real_smul, vecMulVec_apply]
  refine ⟨⟨hp 1, heq.symm ▸ hp (-1)⟩, hp (-1), ?_⟩
  rw [← heq, sub_sub_cancel]
  exact hp 1

/-- The positive-part matrix-element bound keeps all original repairs and both event signs. -/
theorem raw_xz_bound (eps : ℝ) (S : Matrix Wire Wire ℂ)
    (sigma : Matrix (Fin 2) (Fin 2) ℂ) (hS : Causal S sigma) :
    (max (Real.sqrt eps - testerNorm (candidate eps - S)) 0) ^ 2 ≤ (sigma 1 1).re := by
  let d := testerNorm (candidate eps - S)
  let P := S.submatrix mainAddress mainAddress
  obtain ⟨hp, hp1, hP, h0, h1, h2⟩ := causal_principal_block_budgets S sigma hS
  have ht (s : ℝ) (hs : EventInterval (compressedNormalization 1 1) (xzEffect s)) :
      Tester (diagonalTester 1 1) (embedBlock (xzEffect s)) :=
    ⟨diagonalTester_pos 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      diagonalTester_normalized 1 1,
      lift_compressed_event 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hs⟩
  have hsym := congrArg Complex.re (hS.1.isHermitian.apply (mainAddress 0) (mainAddress 2))
  simp only [Complex.star_def, Complex.conj_re] at hsym
  have hv : response (candidate eps - S) (embedBlock (xzEffect 1)) -
      response (candidate eps - S) (embedBlock (xzEffect (-1))) =
        2 * (Real.sqrt eps - (P 0 2).re) := by
    change eventResponse _ _ - eventResponse _ _ = _
    rw [response_compressed_event, response_compressed_event]
    simp [eventResponse, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three, xzEffect_apply,
      Matrix.smul_apply, Pi.smul_apply, Pi.star_apply, Complex.real_smul, vecMulVec_apply, Complex.mul_re,
      candidate, candidateVector, mainAddress, P]
    simp [mainAddress] at hsym
    linarith
  obtain ⟨_, _, _, _, hb⟩ := tester_norm_attained (candidate eps - S)
  have hplus := abs_le.mp (hb _ _ (ht 1 xz_effect_intervals.1))
  have hminus := abs_le.mp (hb _ _ (ht (-1) xz_effect_intervals.2))
  have hlo : Real.sqrt eps - d ≤ (P 0 2).re := by dsimp [d]; linarith
  have hs := D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.psd_entry_bound hP 0 2
  have hm := mul_le_mul (h0.trans (by linarith : 1 - (sigma 1 1).re ≤ 1)) h2
    (Complex.nonneg_iff.mp (hP.diag_nonneg (i := 2))).1 (by norm_num : (0 : ℝ) ≤ 1)
  simp only [Complex.normSq_apply, one_mul] at hs hm
  have hsq : (P 0 2).re ^ 2 ≤ (sigma 1 1).re := by nlinarith [sq_nonneg (P 0 2).im]
  by_cases hn : 0 ≤ Real.sqrt eps - d
  · rw [max_eq_left hn]
    nlinarith
  · rw [max_eq_right (le_of_not_ge hn), zero_pow (by decide : 2 ≠ 0)]
    exact hp

/-- Every original optimizer, without a symmetry or support assumption, lies in the interval. -/
theorem all_original_optimizer_localization (eps : ℝ) (he : 0 < eps) (he16 : eps ≤ 1 / 16)
    (S : Matrix Wire Wire ℂ) (sigma : Matrix (Fin 2) (Fin 2) ℂ) (hS : Causal S sigma)
    (hopt : testerNorm (candidate eps - S) = optimalError eps) :
    1 - Real.sqrt (1 - eps) < (sigma 1 1).re ∧ (sigma 1 1).re ≤ eps := by
  let c := Real.sqrt (1 - eps)
  let d := Real.sqrt eps
  let p := (sigma 1 1).re
  have he1 : eps ≤ 1 := by linarith
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcs : c ^ 2 = 1 - eps := Real.sq_sqrt (by linarith)
  have hc : 15 / 16 < c := by nlinarith
  have hc1 : c < 1 := by nlinarith
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hds : d ^ 2 = eps := Real.sq_sqrt he.le
  have hd14 : d ≤ 1 / 4 := by nlinarith
  obtain ⟨hupper, hstrict⟩ := explicit_repair_upper eps he he16
  have hlow := raw_xz_bound eps S sigma hS
  rw [hopt] at hlow
  constructor
  · let w := d - 9 * eps / 8
    have hw : (23 / 32) * d ≤ w := by
      dsimp [w]
      nlinarith [mul_le_mul_of_nonneg_left hd14 hd0]
    have hw0 : 0 ≤ w := (mul_nonneg (by norm_num) hd0).trans hw
    have hwm : w ≤ max (d - optimalError eps) 0 := by
      apply le_trans _ (le_max_left _ _)
      dsimp [w]
      linarith
    have hmax0 : 0 ≤ max (d - optimalError eps) 0 := le_max_right _ _
    have hwsq : w ^ 2 ≤ p := by
      have hs := mul_nonneg (sub_nonneg.mpr hwm) (add_nonneg hmax0 hw0)
      change max (d - optimalError eps) 0 ^ 2 ≤ p at hlow
      nlinarith
    have hcoef : 529 * eps / 1024 ≤ p := by
      have hs := mul_nonneg (sub_nonneg.mpr hw)
        (add_nonneg hw0 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 23 / 32) hd0))
      nlinarith
    have hg := mul_pos (sub_pos.mpr hc1) (sub_pos.mpr hc)
    change 1 - c < p
    nlinarith
  · let q := c / (1 + 3 * c)
    have hden : 0 < 1 + 3 * c := by positivity
    have hq : 0 < q := div_pos (by linarith) hden
    have hq1 : q < 1 := (div_lt_iff₀ hden).mpr (by linarith)
    have hg : 0 < 4 * q * (1 - q) := by positivity
    have hb := raw_full_block_dual_barrier eps S sigma he.le he1 hS q hq.le hq1.le
    have hv : eps * (1 - q) + q * (1 - q) * ((1 + c) ^ 2 - 4 * (1 - p)) =
        explicitValue eps + 4 * q * (1 - q) * (p - eps) := by
      change eps * (1 - q) + q * (1 - q) * ((1 + c) ^ 2 - 4 * (1 - p)) =
        eps * (1 + c ^ 2 / ((1 + c) * (1 + 3 * c))) + 4 * q * (1 - q) * (p - eps)
      dsimp [q]
      have heq : eps = 1 - c ^ 2 := by linarith
      rw [heq]
      field_simp
      ring
    change eps * (1 - q) + q * (1 - q) * ((1 + c) ^ 2 - 4 * (1 - p)) ≤ _ at hb
    rw [hv, hopt] at hb
    by_contra hnot
    have hpg : 0 < p - eps := sub_pos.mpr (lt_of_not_ge hnot)
    nlinarith [mul_pos hg hpg]

/-- Original extrema exist, and every optimizer admits an optimal repair at its own marginal. -/
theorem unconditional_same_p_reduction (eps : ℝ) (he : 0 < eps) (he16 : eps ≤ 1 / 16) :
    (∃ S sigma, Causal S sigma ∧ testerNorm (candidate eps - S) = optimalError eps) ∧
      ∀ S sigma, Causal S sigma → testerNorm (candidate eps - S) = optimalError eps →
        let p := (sigma 1 1).re
        (1 - Real.sqrt (1 - eps) < p ∧ p ≤ eps) ∧
        Causal (rankOneRepair p) (diagonalMarginal p) ∧ diagonalMarginal p 1 1 = sigma 1 1 ∧
        testerNorm (candidate eps - rankOneRepair p) = optimalError eps ∧
        ∀ q t : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ t → t ≤ 1 →
          scalarLambda eps p q t + max (eps * (1 - q - t)) 0 ≤ optimalError eps := by
  have h := attained_original_minimum_and_same_p_reduction eps he.le (by linarith)
  refine ⟨h.1, ?_⟩
  intro S sigma hS hopt p
  have hl := all_original_optimizer_localization eps he he16 S sigma hS hopt
  exact ⟨hl, h.2.2 S sigma hS hopt hl.1.le hl.2⟩

private theorem scalar_endpoint (eps p : ℝ) (he : 0 ≤ eps) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    scalarLambda eps p 1 1 = (eps + Real.sqrt
      (eps ^ 2 + 4 * (Real.sqrt eps * Real.sqrt (1 - p) - Real.sqrt p) ^ 2)) / 2 := by
  have hd : (scalarU eps 1 1 + scalarV p 1) ^ 2 - 4 * scalarW eps p 1 1 ^ 2 =
      eps ^ 2 + 4 * (Real.sqrt eps * Real.sqrt (1 - p) - Real.sqrt p) ^ 2 := by
    simp only [scalarU, scalarV, scalarW, sub_self, mul_zero, add_zero, mul_one,
      Real.sqrt_mul he]
    ring_nf
    simp only [Real.sq_sqrt he, Real.sq_sqrt hp, Real.sq_sqrt (sub_nonneg.mpr hp1)]
    ring
  rw [scalarLambda, hd]
  dsimp [scalarU, scalarV]
  ring

/-- Uniform cap over all original optimizers, with the same original marginal retained. -/
private theorem all_original_optimizer_kappa_cap (eps : ℝ) (he : 0 < eps)
    (he16 : eps ≤ 1 / 16) (S : Matrix Wire Wire ℂ) (sigma : Matrix (Fin 2) (Fin 2) ℂ)
    (hS : Causal S sigma) (hopt : testerNorm (candidate eps - S) = optimalError eps) :
    0 ≤ (eps - (sigma 1 1).re) / (eps * Real.sqrt eps) ∧
      (eps - (sigma 1 1).re) / (eps * Real.sqrt eps) ≤ 3 / 4 + Real.sqrt eps := by
  let p := (sigma 1 1).re
  let d := Real.sqrt eps
  let a := Real.sqrt (1 - p)
  let b := Real.sqrt p
  have hd : 0 < d := Real.sqrt_pos.mpr he
  have hds : d ^ 2 = eps := Real.sq_sqrt he.le
  have hden : 0 < eps * d := mul_pos he hd
  obtain ⟨hloc, _, _, _, hscalar⟩ :=
    (unconditional_same_p_reduction eps he he16).2 S sigma hS hopt
  have hp : 0 ≤ p := (causal_principal_block_budgets S sigma hS).1
  have hpe : p ≤ eps := hloc.2
  have hp1 : p ≤ 1 := by linarith
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have has : a ^ 2 = 1 - p := Real.sq_sqrt (sub_nonneg.mpr hp1)
  have hbs : b ^ 2 = p := Real.sq_sqrt hp
  have ha1 : a ≤ 1 := by nlinarith
  have hbd : b ≤ d := by nlinarith
  have hv := hscalar 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [scalar_endpoint eps p he.le hp hp1] at hv
  have hmax : max (eps * (1 - 1 - 1)) 0 = 0 := max_eq_right (by nlinarith)
  rw [hmax, add_zero] at hv
  obtain ⟨hu, hstrict⟩ := explicit_repair_upper eps he he16
  have hsqrt : Real.sqrt (eps ^ 2 + 4 * (d * a - b) ^ 2) ≤ 5 * eps / 4 := by
    change (eps + Real.sqrt (eps ^ 2 + 4 * (d * a - b) ^ 2)) / 2 ≤ _ at hv
    linarith
  have hrad : 0 ≤ eps ^ 2 + 4 * (d * a - b) ^ 2 := by positivity
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (eps ^ 2 + 4 * (d * a - b) ^ 2)
  have hdiff : d * a - b ≤ 3 * eps / 8 := by
    nlinarith [sq_nonneg (3 * eps / 8 + (d * a - b))]
  have hsum : d * a + b ≤ 2 * d := by nlinarith [mul_le_mul_of_nonneg_left ha1 hd.le]
  have hprod := mul_le_mul hdiff hsum (by positivity : 0 ≤ d * a + b)
    (by positivity : 0 ≤ 3 * eps / 8)
  have hid : (d * a - b) * (d * a + b) = eps * (1 - p) - p := by
    nlinarith [show (d * a) ^ 2 = eps * (1 - p) by rw [mul_pow, hds, has]]
  rw [hid] at hprod
  refine ⟨div_nonneg (sub_nonneg.mpr hpe) hden.le, (div_le_iff₀ hden).mpr ?_⟩
  have hpp := mul_le_mul_of_nonneg_left hpe he.le
  change eps - p ≤ (3 / 4 + d) * (eps * d)
  nlinarith [show eps * d ^ 2 = eps ^ 2 by rw [hds]; ring]

private theorem original_value_lower_rate (eps : ℝ) (he : 0 < eps) (he16 : eps ≤ 1 / 16) :
    -9 / 16 - 15 * Real.sqrt eps / 16 ≤
      (optimalError eps - 9 * eps / 8) / (eps * Real.sqrt eps) := by
  obtain ⟨S, sigma, hS, hopt, _⟩ := original_minimum_attained eps
  have hk := (all_original_optimizer_kappa_cap eps he he16 S sigma hS hopt).2
  have hd : 0 < Real.sqrt eps := Real.sqrt_pos.mpr he
  have hden : 0 < eps * Real.sqrt eps := mul_pos he hd
  have hp := (div_le_iff₀ hden).mp hk
  have hb := raw_full_block_dual_barrier eps S sigma he.le (by linarith) hS
    (1 / 4) (by norm_num) (by norm_num)
  rw [hopt] at hb
  have hc : 0 ≤ Real.sqrt (1 - eps) := Real.sqrt_nonneg _
  have hcs : Real.sqrt (1 - eps) ^ 2 = 1 - eps := Real.sq_sqrt (by linarith)
  have hc1 : Real.sqrt (1 - eps) ≤ 1 := by nlinarith
  have hce : 1 - Real.sqrt (1 - eps) ≤ eps := by
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hc1)]
  have hsmall : (1 - Real.sqrt (1 - eps)) ^ 2 ≤ eps ^ 2 := by nlinarith
  have hds := Real.sq_sqrt he.le
  have hlast : eps * Real.sqrt eps * Real.sqrt eps = eps ^ 2 := by nlinarith
  apply (le_div_iff₀ hden).mpr
  nlinarith

private theorem scalar_wedge_formula (eps p q t : ℝ) (he : 0 ≤ eps) (he1 : eps ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    scalarLambda eps p q t = ((p - eps + eps * q + (eps - p) * t) +
      Real.sqrt ((p - eps + eps * q + (eps - p) * t) ^ 2 + 4 *
        ((Real.sqrt (1 - p) * (1 - Real.sqrt (1 - eps))) ^ 2 * q * (1 - q) +
          (Real.sqrt p - Real.sqrt eps * Real.sqrt (1 - p)) ^ 2 * q * t +
          (Real.sqrt (1 - eps) * Real.sqrt p - Real.sqrt eps * Real.sqrt (1 - p)) ^ 2 *
            (1 - q) * t))) / 2 := by
  have hd : (scalarU eps q t + scalarV p t) ^ 2 - 4 * scalarW eps p q t ^ 2 =
      (p - eps + eps * q + (eps - p) * t) ^ 2 + 4 *
        ((Real.sqrt (1 - p) * (1 - Real.sqrt (1 - eps))) ^ 2 * q * (1 - q) +
          (Real.sqrt p - Real.sqrt eps * Real.sqrt (1 - p)) ^ 2 * q * t +
          (Real.sqrt (1 - eps) * Real.sqrt p - Real.sqrt eps * Real.sqrt (1 - p)) ^ 2 *
            (1 - q) * t) := by
    simp only [scalarU, scalarV, scalarW, Real.sqrt_mul he]
    ring_nf
    simp only [Real.sq_sqrt he, Real.sq_sqrt hp, Real.sq_sqrt (sub_nonneg.mpr he1),
      Real.sq_sqrt (sub_nonneg.mpr hp1)]
    ring
  rw [scalarLambda, hd]
  dsimp [scalarU, scalarV]
  ring

private theorem ratio_square_bounds (d k n v : ℝ) (hd : 0 < d) (hd1 : d ≤ 1 / 64)
    (hk : 0 ≤ k) (hk1 : k ≤ 7 / 8) (hn : 0 ≤ n) (hnk : n ≤ k)
    (hv : 15 / 8 ≤ v) (hv2 : 2 - 2 * d ≤ v) :
    (n / v) ^ 2 ≤ 2 / 9 ∧ (n / v) ^ 2 ≤ k ^ 2 / 4 + d := by
  have hv0 : 0 < v := by linarith
  have hn2 : n ^ 2 ≤ k ^ 2 := by nlinarith
  have hk2 : k ^ 2 ≤ 1 := by nlinarith
  have hv2sq : (2 - 2 * d) ^ 2 ≤ v ^ 2 := by nlinarith
  rw [div_pow]
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hv0)).mpr
    nlinarith
  · apply (div_le_iff₀ (sq_pos_of_pos hv0)).mpr
    have hinv : 1 ≤ (1 / 4 + d) * (2 - 2 * d) ^ 2 := by
      nlinarith [mul_nonneg hd.le (show 0 ≤ 2 - 7 * d by linarith),
        mul_nonneg hd.le (sq_nonneg d)]
    have h1 := mul_le_mul_of_nonneg_left hinv (sq_nonneg k)
    have h2 := mul_le_mul_of_nonneg_right
      (show k ^ 2 * (1 / 4 + d) ≤ k ^ 2 / 4 + d by
        nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hk2)]) (sq_nonneg (2 - 2 * d))
    have h3 := mul_le_mul_of_nonneg_left hv2sq
      (show 0 ≤ k ^ 2 / 4 + d by positivity)
    nlinarith

set_option maxHeartbeats 800000 in
-- The three rationalized coefficients share polynomial normalization and square-root bounds.
private theorem scaled_scalar_data (d k : ℝ) (hd : 0 < d) (hd1 : d ≤ 1 / 64)
    (hk : 1 / 2 ≤ k) (hk1 : k ≤ 7 / 8) :
    let p := d ^ 2 - k * d ^ 3
    0 ≤ p ∧ p ≤ 1 ∧ ∃ A B C : ℝ,
      |A - 1 / 4| ≤ d ^ 2 ∧ 0 ≤ A ∧ 0 ≤ B ∧ B ≤ 2 / 9 ∧
      0 ≤ C ∧ C ≤ 2 / 9 ∧ B ≤ k ^ 2 / 4 + d ∧ C ≤ k ^ 2 / 4 + d ∧
      ∀ q t : ℝ, scalarLambda (d ^ 2) p q t = d ^ 2 *
        ((q + k * d * (t - 1) + Real.sqrt ((q + k * d * (t - 1)) ^ 2 +
          4 * (A * q * (1 - q) + B * q * t + C * (1 - q) * t))) / 2) := by
  intro p
  let c := Real.sqrt (1 - d ^ 2)
  let a := Real.sqrt (1 - p)
  let u := Real.sqrt (1 - k * d)
  have hk0 : 0 ≤ k := by linarith
  have hkd : 0 ≤ k * d := mul_nonneg hk0 hd.le
  have hkd1 : k * d ≤ d := mul_le_of_le_one_left hd.le (by linarith)
  have hd2 : d ^ 2 ≤ d := by nlinarith
  have hp : 0 ≤ p := by
    dsimp [p]
    have h := mul_nonneg (sq_nonneg d) (show 0 ≤ 1 - k * d by linarith)
    nlinarith only [h]
  have hpd : p ≤ d ^ 2 := sub_le_self _ (mul_nonneg hk0 (pow_nonneg hd.le _))
  have hp1 : p ≤ 1 := by nlinarith only [hpd, hd, hd1]
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hcs : c ^ 2 = 1 - d ^ 2 := Real.sq_sqrt (by nlinarith only [hd, hd1])
  have has : a ^ 2 = 1 - p := Real.sq_sqrt (by linarith)
  have hus : u ^ 2 = 1 - k * d := Real.sq_sqrt (by linarith)
  have hc1 : c ≤ 1 := by nlinarith only [hcs, hc0, sq_nonneg d]
  have ha1 : a ≤ 1 := by nlinarith only [has, ha0, hp]
  have hu1 : u ≤ 1 := by nlinarith only [hus, hu0, hkd]
  have hcl : 1 - d ^ 2 ≤ c := by nlinarith only [hcs, mul_nonneg hc0 (sub_nonneg.mpr hc1)]
  have hal : 1 - d ^ 2 ≤ a := by nlinarith only [has, hpd, mul_nonneg ha0 (sub_nonneg.mpr ha1)]
  have hul : 1 - k * d ≤ u := by nlinarith only [hus, mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have hc63 : 63 / 64 ≤ c := by nlinarith only [hcl, hd2, hd1]
  have ha63 : 63 / 64 ≤ a := by nlinarith only [hal, hd2, hd1]
  have hu63 : 63 / 64 ≤ u := by nlinarith only [hul, hkd1, hd1]
  have hbden : 15 / 8 ≤ u + a := by linarith
  have hcden : 15 / 8 ≤ c * u + a := by
    nlinarith only [ha63, mul_le_mul hc63 hu63 (by norm_num) hc0]
  have hbden2 : 2 - 2 * d ≤ u + a := by nlinarith only [hul, hal, hkd1, hd2]
  have hcden2 : 2 - 2 * d ≤ c * u + a := by
    have h := mul_nonneg (sub_nonneg.mpr hcl) hu0
    have h2 := mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hu1)
    nlinarith only [h, h2, hul, hal, hkd1, hd, hd1]
  have hnum : 0 ≤ k - d + k * d ^ 2 := by
    nlinarith only [hk, hd1, mul_nonneg hk0 (sq_nonneg d)]
  have hnumk : k - d + k * d ^ 2 ≤ k := by
    nlinarith only [mul_nonneg hd.le (show 0 ≤ 1 - k * d by linarith)]
  let A := (a / (1 + c)) ^ 2
  let B := ((k - d + k * d ^ 2) / (u + a)) ^ 2
  let C := (k / (c * u + a)) ^ 2
  obtain ⟨hB, hBk⟩ := ratio_square_bounds d k (k - d + k * d ^ 2) (u + a)
    hd hd1 hk0 hk1 hnum hnumk hbden hbden2
  obtain ⟨hC, hCk⟩ := ratio_square_bounds d k k (c * u + a)
    hd hd1 hk0 hk1 hk0 le_rfl hcden hcden2
  have hA : |A - 1 / 4| ≤ d ^ 2 := by
    have hden : 0 < (1 + c) ^ 2 := by positivity
    have hdd : d ^ 2 * (1 + c) ^ 2 ≥ d ^ 2 := by
      have h := mul_nonneg (sq_nonneg d) (show 0 ≤ (1 + c) ^ 2 - 1 by nlinarith only [hc0])
      nlinarith only [h]
    apply abs_le.mpr
    constructor
    · change -(d ^ 2) ≤ (a / (1 + c)) ^ 2 - 1 / 4
      rw [le_sub_iff_add_le, div_pow]
      apply (le_div_iff₀ hden).mpr
      nlinarith only [has, hpd, hdd, hc1, hc0, hcs]
    · change (a / (1 + c)) ^ 2 - 1 / 4 ≤ d ^ 2
      rw [sub_le_iff_le_add, div_pow]
      apply (div_le_iff₀ hden).mpr
      nlinarith only [has, hp, hcs, hcl, hdd]
  refine ⟨hp, hp1, A, B, C, hA, sq_nonneg _, sq_nonneg _, hB,
    sq_nonneg _, hC, hBk, hCk, ?_⟩
  intro q t
  have hpsqrt : Real.sqrt p = d * u := by
    apply (Real.sqrt_eq_iff_eq_sq hp (mul_nonneg hd.le hu0)).mpr
    rw [mul_pow, hus]
    dsimp [p]
    ring
  have hdsqrt : Real.sqrt (d ^ 2) = d := Real.sqrt_sq hd.le
  have hxy : a * (1 - c) = d ^ 2 * (a / (1 + c)) := by
    field_simp [show 1 + c ≠ 0 by linarith]
    nlinarith only [hcs]
  have hxz : d * u - d * a = -(d ^ 2) * ((k - d + k * d ^ 2) / (u + a)) := by
    field_simp [show u + a ≠ 0 by linarith]
    dsimp [p] at has
    nlinarith only [hus, has]
  have hyz : c * (d * u) - d * a = -(d ^ 2) * (k / (c * u + a)) := by
    field_simp [show c * u + a ≠ 0 by linarith]
    have hcu : (c * u) ^ 2 = (1 - d ^ 2) * (1 - k * d) := by rw [mul_pow, hcs, hus]
    dsimp [p] at has
    nlinarith only [hcu, has]
  rw [scalar_wedge_formula (d ^ 2) p q t (sq_nonneg _) (by nlinarith only [hd, hd1]) hp hp1,
    hdsqrt, hpsqrt]
  change ((p - d ^ 2 + d ^ 2 * q + (d ^ 2 - p) * t) + Real.sqrt
    ((p - d ^ 2 + d ^ 2 * q + (d ^ 2 - p) * t) ^ 2 +
      4 * ((a * (1 - c)) ^ 2 * q * (1 - q) + (d * u - d * a) ^ 2 * q * t +
        (c * (d * u) - d * a) ^ 2 * (1 - q) * t))) / 2 = _
  rw [hxy, hxz, hyz]
  have hT : p - d ^ 2 + d ^ 2 * q + (d ^ 2 - p) * t =
      d ^ 2 * (q + k * d * (t - 1)) := by dsimp [p]; ring
  rw [hT]
  have hrad : (d ^ 2 * (q + k * d * (t - 1))) ^ 2 +
      4 * ((d ^ 2 * (a / (1 + c))) ^ 2 * q * (1 - q) +
        (-(d ^ 2) * ((k - d + k * d ^ 2) / (u + a))) ^ 2 * q * t +
        (-(d ^ 2) * (k / (c * u + a))) ^ 2 * (1 - q) * t) =
      (d ^ 2) ^ 2 * ((q + k * d * (t - 1)) ^ 2 +
        4 * (A * q * (1 - q) + B * q * t + C * (1 - q) * t)) := by
    dsimp [A, B, C]; ring
  rw [hrad, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg d)]
  ring

private theorem quadratic_root_upper (T Q z : ℝ) (hQ : 0 ≤ Q) (hz : 0 < z)
    (hpoly : 0 ≤ z ^ 2 - T * z - Q) :
    (T + Real.sqrt (T ^ 2 + 4 * Q)) / 2 ≤ z := by
  have hT : T ≤ z := by nlinarith
  have hs : Real.sqrt (T ^ 2 + 4 * Q) ≤ 2 * z - T :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  linarith

private theorem uniform_negative_certificate (d h a b c q t : ℝ)
    (hd : 0 < d) (hd1 : d ≤ 1 / 64) (hh : 0 ≤ h) (hhd : h ≤ d)
    (ha : |a - 1 / 4| ≤ d ^ 2) (ha0 : 0 ≤ a)
    (hb : 0 ≤ b) (hb1 : b ≤ 2 / 9) (hc : 0 ≤ c) (hc1 : c ≤ 2 / 9)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) :
    ((q + h * (t - 1)) + Real.sqrt ((q + h * (t - 1)) ^ 2 +
      4 * (a * q * (1 - q) + b * q * t + c * (1 - q) * t))) / 2 + 1 - q - t ≤
      9 / 8 - 3 * h / 4 + 4 * d ^ 2 := by
  let m := 1 / 8 - 3 * h / 4 + 4 * d ^ 2
  let z := m + q + t
  let T := q + h * (t - 1)
  let Q := a * q * (1 - q) + b * q * t + c * (1 - q) * t
  have hm : 1 / 9 < m := by dsimp [m]; nlinarith [sq_nonneg d]
  have hz : 0 < z := by dsimp [z]; linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hqq : 0 ≤ q * (1 - q) := mul_nonneg hq (sub_nonneg.mpr hq1)
  have hqq1 : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  have hhs : h ^ 2 ≤ d ^ 2 := by nlinarith
  have had : -(d ^ 2) ≤ a - 1 / 4 ∧ a - 1 / 4 ≤ d ^ 2 := abs_le.mp ha
  have hpert : -(d ^ 2) / 4 ≤ (a - 1 / 4) * (q ^ 2 - q) := by
    have h1 := mul_le_mul_of_nonneg_right had.2 hqq
    have h2 := mul_le_mul_of_nonneg_left hqq1 (sq_nonneg d)
    nlinarith
  have hbase : d ^ 2 / 2 ≤ 4 * d ^ 2 * (q + 1 / 4 - h / 2) := by
    have h := mul_nonneg (sq_nonneg d) (show 0 ≤ q + 1 / 8 - h / 2 by linarith)
    nlinarith
  have hP : 0 ≤ a * q ^ 2 + (m + h - a) * q + m * (m + h) := by
    have heq : a * q ^ 2 + (m + h - a) * q + m * (m + h) =
        (q - 1 / 4 + h / 2) ^ 2 / 4 - h ^ 2 / 4 +
        4 * d ^ 2 * (q + 1 / 4 - h / 2) + 16 * (d ^ 2) ^ 2 +
        (a - 1 / 4) * (q ^ 2 - q) := by dsimp [m]; ring
    rw [heq]
    nlinarith [sq_nonneg (q - 1 / 4 + h / 2), sq_nonneg (d ^ 2)]
  have hcoef : 0 ≤ m * (2 - h) + h - c + q * (1 - h - b + c) := by
    have h1 := mul_le_mul_of_nonneg_right hm.le (show 0 ≤ 2 - h by linarith)
    have h2 := mul_nonneg hq (show 0 ≤ 1 - h - b + c by linarith)
    nlinarith
  have hpoly : 0 ≤ z ^ 2 - T * z - Q := by
    have heq : z ^ 2 - T * z - Q =
        a * q ^ 2 + (m + h - a) * q + m * (m + h) +
        t * (m * (2 - h) + h - c + q * (1 - h - b + c)) + (1 - h) * t ^ 2 := by
      dsimp [z, T, Q]; ring
    rw [heq]
    exact add_nonneg (add_nonneg hP (mul_nonneg ht hcoef))
      (mul_nonneg (by linarith) (sq_nonneg t))
  have hr := quadratic_root_upper T Q z hQ hz hpoly
  change (T + Real.sqrt (T ^ 2 + 4 * Q)) / 2 + 1 - q - t ≤ _
  dsimp [z, m] at hr
  linarith

private theorem matched_competitor_upper (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1 / 4096) :
    optimalError (d ^ 2) ≤ d ^ 2 *
      (9 / 8 - 9 * d / 16 + 3 * d * Real.sqrt d / 4 + 4 * d ^ 2) := by
  let k := 3 / 4 - Real.sqrt d
  let p := d ^ 2 - k * d ^ 3
  let target := 9 / 8 - 3 * (k * d) / 4 + 4 * d ^ 2
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hss : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd.le
  have hs64 : Real.sqrt d ≤ 1 / 64 := by nlinarith only [hss, hs, hd1]
  have hk : 1 / 2 ≤ k := by dsimp [k]; linarith
  have hk1 : k ≤ 7 / 8 := by dsimp [k]; linarith
  have hkd : 0 ≤ k * d := mul_nonneg (by linarith) hd.le
  have hkd1 : k * d ≤ d := mul_le_of_le_one_left hd.le (by linarith)
  obtain ⟨hp, hp1, A, B, C, hA, hA0, hB0, hB, hC0, hC, hBk, hCk, hf⟩ :=
    scaled_scalar_data d k hd (by linarith) hk hk1
  have htarget : 9 / 8 - d ≤ target := by
    dsimp [target]
    nlinarith only [hkd1, sq_nonneg d, hd]
  have hscalar : ∀ q t : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ t → t ≤ 1 →
      scalarLambda (d ^ 2) p q t + max (d ^ 2 * (1 - q - t)) 0 ≤ d ^ 2 * target := by
    intro q t hq hq1 ht ht1
    let T := q + k * d * (t - 1)
    let Q := A * q * (1 - q) + B * q * t + C * (1 - q) * t
    let root := (T + Real.sqrt (T ^ 2 + 4 * Q)) / 2
    have hQ : 0 ≤ Q := by dsimp [Q]; positivity
    have hneg : root + 1 - q - t ≤ target :=
      uniform_negative_certificate d (k * d) A B C q t hd (by linarith) hkd hkd1
        hA hA0 hB0 hB hC0 hC hq hq1 ht
    have hpos : root ≤ target := by
      let z := 9 / 8 - d
      have hz : 1 ≤ z := by dsimp [z]; linarith
      have hT : T ≤ q := by
        dsimp [T]
        nlinarith only [mul_nonneg hkd (sub_nonneg.mpr ht1)]
      have hA1 : A ≤ 1 := by
        have h := (abs_le.mp hA).2
        nlinarith only [h, hd, hd1]
      have hAq : A * q ≤ 1 := (mul_le_mul hA1 hq1 hq (by norm_num)).trans_eq (by norm_num)
      have hQt : Q ≤ A * q * (1 - q) + (k ^ 2 / 4 + d) := by
        have h1 := mul_le_mul_of_nonneg_right hBk (mul_nonneg hq ht)
        have h2 := mul_le_mul_of_nonneg_right hCk
          (mul_nonneg (sub_nonneg.mpr hq1) ht)
        have h3 := mul_le_mul_of_nonneg_left ht1 (show 0 ≤ k ^ 2 / 4 + d by positivity)
        dsimp [Q]
        nlinarith only [h1, h2, h3]
      have hbase : k ^ 2 / 4 + d ≤ z ^ 2 - z := by
        dsimp [k, z]
        nlinarith only [hss, mul_nonneg hs (show 0 ≤ 3 / 8 - 5 * Real.sqrt d / 2 by linarith),
          sq_nonneg d]
      have hpoly : 0 ≤ z ^ 2 - T * z - Q := by
        have h1 := mul_le_mul_of_nonneg_right hT (by linarith : 0 ≤ z)
        have h2 := mul_nonneg (sub_nonneg.mpr hq1) (show 0 ≤ z - A * q by linarith)
        nlinarith only [h1, h2, hQt, hbase]
      exact (quadratic_root_upper T Q z hQ (by linarith) hpoly).trans htarget
    rw [hf q t, add_max, add_zero]
    change max (d ^ 2 * root + d ^ 2 * (1 - q - t)) (d ^ 2 * root) ≤ _
    apply max_le
    · have h := mul_le_mul_of_nonneg_left hneg (sq_nonneg d)
      nlinarith only [h]
    · exact mul_le_mul_of_nonneg_left hpos (sq_nonneg d)
  have he1 : d ^ 2 ≤ 1 := by nlinarith only [hd, hd1]
  have hn := tester_norm_le ((rank_one_full_objective (d ^ 2) p (d ^ 2 * target)
    (sq_nonneg _) he1 hp hp1).mpr hscalar)
  obtain ⟨h0, h1, h2⟩ := rankOneBlock_budgets p hp hp1
  have hR := (compressed_block_causal_lift p (rankOneBlock p) hp hp1
    (rankOneBlock_pos p) h0.le h1.le h2.le).1
  obtain ⟨_, _, _, _, hmin⟩ := original_minimum_attained (d ^ 2)
  have h := (hmin _ _ hR).trans hn
  calc
    _ ≤ d ^ 2 * target := h
    _ = _ := by dsimp [target, k]; ring

private theorem uniform_original_rates (eps : ℝ) (he : 0 < eps)
    (hsmall : Real.sqrt eps ≤ 1 / 4096) :
    |(optimalError eps - 9 * eps / 8) / (eps * Real.sqrt eps) + 9 / 16| ≤
        3 * Real.sqrt (Real.sqrt eps) / 4 + 4 * Real.sqrt eps ∧
      ∀ S sigma, Causal S sigma → testerNorm (candidate eps - S) = optimalError eps →
        |(eps - (sigma 1 1).re) / (eps * Real.sqrt eps) - 3 / 4| ≤
          Real.sqrt (Real.sqrt eps) + 6 * Real.sqrt eps := by
  let d := Real.sqrt eps
  have hd : 0 < d := Real.sqrt_pos.mpr he
  have hds : d ^ 2 = eps := Real.sq_sqrt he.le
  have he16 : eps ≤ 1 / 16 := by change d ≤ 1 / 4096 at hsmall; nlinarith
  have hden : 0 < eps * d := mul_pos he hd
  have hs : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hupper := matched_competitor_upper d hd hsmall
  rw [hds] at hupper
  have hlo := original_value_lower_rate eps he he16
  have hlast : eps * d * d = eps ^ 2 := by
    calc
      _ = eps * d ^ 2 := by ring
      _ = eps ^ 2 := by rw [hds]; ring
  have hu : (optimalError eps - 9 * eps / 8) / (eps * d) ≤
      -9 / 16 + 3 * Real.sqrt d / 4 + 4 * d := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hupper, hlast]
  constructor
  · apply abs_le.mpr
    change -9 / 16 - 15 * d / 16 ≤ _ at hlo
    constructor <;> linarith
  · intro S sigma hS hopt
    have hk := (all_original_optimizer_kappa_cap eps he he16 S sigma hS hopt).2
    have hb := raw_full_block_dual_barrier eps S sigma he.le (by linarith) hS
      (1 / 4) (by norm_num) (by norm_num)
    rw [hopt] at hb
    have hc : 0 ≤ Real.sqrt (1 - eps) := Real.sqrt_nonneg _
    have hcs : Real.sqrt (1 - eps) ^ 2 = 1 - eps := Real.sq_sqrt (by linarith)
    have hc1 : Real.sqrt (1 - eps) ≤ 1 := by nlinarith
    have hce : 1 - Real.sqrt (1 - eps) ≤ eps := by
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hc1)]
    have hsq : (1 - Real.sqrt (1 - eps)) ^ 2 ≤ eps ^ 2 := by nlinarith
    have hkl : 3 / 4 - Real.sqrt d - 6 * d ≤
        (eps - (sigma 1 1).re) / (eps * d) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith only [hb, hcs, hsq, hupper, hlast, sq_nonneg eps]
    apply abs_le.mpr
    constructor <;> linarith

/-- The original complex problem has minimizers, and both next-order limits hold uniformly
for every original minimizing pair with one common threshold. -/
theorem theorem_61_1 :
    (∀ eps : ℝ, 0 < eps → eps ≤ 1 / 16 →
      ∃ S sigma, Causal S sigma ∧ testerNorm (candidate eps - S) = optimalError eps) ∧
    ∀ alpha : ℝ, 0 < alpha → ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ eps : ℝ, 0 < eps → eps < min eps0 (1 / 16) →
        |(optimalError eps - 9 * eps / 8) / (eps * Real.sqrt eps) + 9 / 16| < alpha ∧
        ∀ S sigma, Causal S sigma → testerNorm (candidate eps - S) = optimalError eps →
          |(eps - (sigma 1 1).re) / (eps * Real.sqrt eps) - 3 / 4| < alpha := by
  constructor
  · intro eps _ _
    obtain ⟨S, sigma, hS, hopt, _⟩ := original_minimum_attained eps
    exact ⟨S, sigma, hS, hopt⟩
  · intro alpha ha
    let r := min (alpha / 8) (1 / 4096)
    have hr : 0 < r := lt_min (by positivity) (by norm_num)
    have hra : r ≤ alpha / 8 := min_le_left _ _
    have hr1 : r ≤ 1 / 4096 := min_le_right _ _
    refine ⟨r ^ 4, pow_pos hr _, ?_⟩
    intro eps he he0
    have her : eps < r ^ 4 := he0.trans_le (min_le_left _ _)
    have hdr : Real.sqrt eps < r ^ 2 :=
      (Real.sqrt_lt he.le (sq_nonneg r)).mpr (by nlinarith only [her])
    have hsr : Real.sqrt (Real.sqrt eps) < r :=
      (Real.sqrt_lt (Real.sqrt_nonneg _) hr.le).mpr hdr
    have hd1 : Real.sqrt eps ≤ 1 / 4096 := by nlinarith
    obtain ⟨hv, hp⟩ := uniform_original_rates eps he hd1
    have hs := Real.sqrt_nonneg (Real.sqrt eps)
    have hss := Real.sq_sqrt (Real.sqrt_nonneg eps)
    have hds : Real.sqrt eps ≤ Real.sqrt (Real.sqrt eps) := by
      nlinarith [mul_nonneg hs (show 0 ≤ 1 - Real.sqrt (Real.sqrt eps) by linarith)]
    refine ⟨hv.trans_lt (by linarith), ?_⟩
    intro S sigma hS hopt
    exact (hp S sigma hS hopt).trans_lt (by linarith)

end D5.S3.Quantum.Foundation.TwoRoundOptimalAsymptotics
