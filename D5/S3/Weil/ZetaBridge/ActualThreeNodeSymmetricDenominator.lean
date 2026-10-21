/- GID: D5/S3/Weil/ZetaBridge/ActualThreeNodeSymmetricDenominator
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualThreeNodeSymmetricDenominator
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: The literal positive and negative exterior columns have the same exact squared three-node denominator. -/

import D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteEnergy

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder Matrix Topology
open D5.S3.Weil.ZetaBridge
open Polynomial MeasureTheory
open ActualThreeNodeSourceHeadBridge ActualThreeNodeFiniteEnergy
open ActualPairedReciprocal ActualNodalCoercivity ActualNodalTailEnclosure
open WeilArithmeticCouplingJet WeilArithmeticCouplingParityGram PrimeSymbolResonance
open D5.S3.Analytic.PolynomialReciprocalBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeSymmetricDenominator

/-- Exact single-source denominator. Its sign is retained until after norm square. -/
lemma actual_single_symmetric_denominator {n : ℤ} (hn : n ≠ 0) (c N : ℕ)
    (hN : 0 < N) (v : ℤ → ℂ) (m : ℤ) (hm : m ≠ 0) (hmS : m ∉ threeNodes n) :
    Real.pi ^ 2 * (1 - ((n : ℝ) / (m : ℝ)) ^ 2) ^ 2 *
        ‖couplingColumn c (threeNodes n) v m‖ ^ 2 =
      ‖value (reciprocalPolynomial 3 N (P c (threeNodes n) v)) ((N : ℝ) / m) -
          (arithmeticBoundarySymbol c m : ℂ) *
            value (reciprocalPolynomial 3 N (Q (threeNodes n) v)) ((N : ℝ) / m)‖ ^ 2 /
        (m : ℝ) ^ 2 := by
  have hSne : (threeNodes n).Nonempty := by simp [threeNodes]
  have hmodel := actual_nodal_polynomial_model c (threeNodes n) hSne v
  have hP : (P c (threeNodes n) v).natDegree < 3 := by
    simpa only [threeNodes_card hn] using hmodel.1
  have hQ : (Q (threeNodes n) v).natDegree < 3 := by
    simpa only [threeNodes_card hn] using hmodel.2.1
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hp := reciprocalPolynomial_exact (by norm_num : 1 ≤ 3) hN
    (P c (threeNodes n) v) hP (m : ℂ) hmC
  have hq := reciprocalPolynomial_exact (by norm_num : 1 ≤ 3) hN
    (Q (threeNodes n) v) hQ (m : ℂ) hmC
  have harg : (N : ℂ) / (m : ℂ) = (((N : ℝ) / m : ℝ) : ℂ) := by push_cast; rfl
  norm_num at hp hq
  rw [harg] at hp hq
  have hnum : (Real.pi : ℂ) * (D (threeNodes n)).eval (m : ℂ) *
      couplingColumn c (threeNodes n) v m =
      (m : ℂ) ^ 2 *
        (value (reciprocalPolynomial 3 N (P c (threeNodes n) v)) ((N : ℝ) / m) -
          (arithmeticBoundarySymbol c m : ℂ) *
            value (reciprocalPolynomial 3 N (Q (threeNodes n) v)) ((N : ℝ) / m)) := by
    rw [hmodel.2.2 m hmS, ← hp, ← hq]
    unfold value
    ring
  have hd : (D (threeNodes n)).eval (m : ℂ) =
      (((m : ℝ) * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2) : ℝ) : ℂ) := by
    rw [(actual_three_nodal hn c v).1]
    simp only [eval_mul, eval_sub, eval_X, eval_pow, eval_C]
    push_cast <;> ring
  have hnorm := congrArg (fun z : ℂ => ‖z‖ ^ 2) hnum
  rw [hd] at hnorm
  have hbase : Real.pi ^ 2 * ((m : ℝ) * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2)) ^ 2 *
      ‖couplingColumn c (threeNodes n) v m‖ ^ 2 =
      (m : ℝ) ^ 4 *
        ‖value (reciprocalPolynomial 3 N (P c (threeNodes n) v)) ((N : ℝ) / m) -
          (arithmeticBoundarySymbol c m : ℂ) *
            value (reciprocalPolynomial 3 N (Q (threeNodes n) v)) ((N : ℝ) / m)‖ ^ 2 := by
    simpa only [norm_mul, norm_pow, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_intCast, sq_abs, ← pow_mul] using hnorm
  have hcancel : Real.pi ^ 2 * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2) ^ 2 *
      ‖couplingColumn c (threeNodes n) v m‖ ^ 2 =
      (m : ℝ) ^ 2 *
        ‖value (reciprocalPolynomial 3 N (P c (threeNodes n) v)) ((N : ℝ) / m) -
          (arithmeticBoundarySymbol c m : ℂ) *
            value (reciprocalPolynomial 3 N (Q (threeNodes n) v)) ((N : ℝ) / m)‖ ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hmr)
    nlinarith only [hbase]
  field_simp [hmr]
  nlinarith only [hcancel]

lemma threeNodes_radius (n : ℤ) :
    ∀ k ∈ threeNodes n, |(k : ℝ)| ≤ |(n : ℝ)| := by
  intro k hk
  simp only [threeNodes, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl <;> simp

/-- Both genuine signs have the SAME squared denominator; neither is discarded. -/
lemma actual_pair_symmetric_denominator {n : ℤ} (hn : n ≠ 0) (c N : ℕ)
    (hN : 0 < N) (hR : |(n : ℝ)| < (N : ℝ)) (v : ℤ → ℂ) (j : ℕ) :
    Real.pi ^ 2 * (1 - ((n : ℝ) / (N + j + 1 : ℕ)) ^ 2) ^ 2 *
        pairedColumnTerm c N (threeNodes n) v j =
      pairedTerm c N
        (reciprocalPolynomial 3 N (P c (threeNodes n) v))
        (reciprocalPolynomial 3 N (Q (threeNodes n) v)) j := by
  let m : ℤ := ((N + j + 1 : ℕ) : ℤ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNm : (N : ℝ) < (m : ℝ) := by
    dsimp [m]
    exact_mod_cast (show N < N + j + 1 by omega)
  have hmp : (0 : ℝ) < m := hNr.trans hNm
  have hm0 : m ≠ 0 := by intro he; simpa [he] using hmp
  have hnot : m ∉ threeNodes n := by
    intro he
    have h := threeNodes_radius n m he
    rw [abs_of_pos hmp] at h
    linarith
  have hnotm : -m ∉ threeNodes n := by
    intro he
    have h := threeNodes_radius n (-m) he
    simp only [Int.cast_neg, abs_neg, abs_of_pos hmp] at h
    linarith
  have hp := actual_single_symmetric_denominator hn c N hN v m hm0 hnot
  have hm := actual_single_symmetric_denominator hn c N hN v (-m)
    (neg_ne_zero.mpr hm0) hnotm
  simp only [Int.cast_neg, div_neg, neg_sq] at hm
  have hs := congrArg₂ (fun x y : ℝ => x + y) hp hm
  convert hs using 1 <;>
    simp only [pairedColumnTerm, pairedTerm, m, Int.cast_natCast] <;> ring

lemma symmetric_factor_bounds {b N m : ℝ} (hN : 0 < N) (hR : |b| < N) (hNm : N < m) :
    0 < (1 - (b / N) ^ 2) ^ 2 ∧
      (1 - (b / N) ^ 2) ^ 2 ≤ (1 - (b / m) ^ 2) ^ 2 ∧
      (1 - (b / m) ^ 2) ^ 2 ≤ 1 := by
  have hm := hN.trans hNm
  have hratN : |b| / N < 1 := (div_lt_one hN).mpr hR
  have hratN0 : 0 ≤ |b| / N := div_nonneg (abs_nonneg _) hN.le
  have hratm0 : 0 ≤ |b| / m := div_nonneg (abs_nonneg _) hm.le
  have hrat : |b| / m ≤ |b| / N :=
    div_le_div_of_nonneg_left (abs_nonneg _) hN hNm.le
  have hsqN : (b / N) ^ 2 < 1 := by
    have hprod : 0 < (1 - |b| / N) * (1 + |b| / N) :=
      mul_pos (sub_pos.mpr hratN) (by linarith)
    have hs : (|b| / N) ^ 2 < 1 := by nlinarith only [hprod]
    simpa only [div_pow, sq_abs] using hs
  have hsq : (b / m) ^ 2 ≤ (b / N) ^ 2 := by
    simpa only [div_pow, sq_abs] using pow_le_pow_left₀ hratm0 hrat 2
  have hbaseN : 0 < 1 - (b / N) ^ 2 := sub_pos.mpr hsqN
  have hbasem : 0 ≤ 1 - (b / m) ^ 2 := by linarith
  refine ⟨sq_pos_of_pos hbaseN, pow_le_pow_left₀ hbaseN.le (by linarith) 2, ?_⟩
  simpa only [one_pow] using
    pow_le_pow_left₀ hbasem (by nlinarith [sq_nonneg (b / m)] : 1 - (b / m) ^ 2 ≤ 1) 2

end D5.S3.Weil.ZetaBridge.ActualThreeNodeSymmetricDenominator
