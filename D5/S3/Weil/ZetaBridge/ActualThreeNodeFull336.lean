/- GID: D5/S3/Weil/ZetaBridge/ActualThreeNodeFull336
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualThreeNodeFull336
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: One vector-independent explicit336 comparison controls the complete original complex three-node Gram in Loewner order. -/

import D5.S3.Weil.ZetaBridge.ActualThreeNodeSymmetricDenominator
import D5.S3.Weil.ZetaBridge.ActualExplicit336

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder Matrix Topology
open D5.S3.Weil.ZetaBridge
open Polynomial MeasureTheory
open ActualThreeNodeSourceHeadBridge ActualThreeNodeFiniteEnergy ActualThreeNodeSymmetricDenominator
open ActualPairedReciprocal ActualNodalCoercivity ActualNodalTailEnclosure
open WeilArithmeticCouplingJet WeilArithmeticCouplingParityGram PrimeSymbolResonance
open D5.S3.Analytic.PolynomialReciprocalBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeFull336

def delta336 (c : ℕ) : ℝ := 9 * 336 * (c : ℝ) ^ 2 * (1 + Real.log (c : ℝ)) ^ 3
def lower336 (c N : ℕ) : ℝ := 1 - delta336 c / N
def upper336 (c N : ℕ) (n : ℤ) : ℝ :=
  (1 + delta336 c / N) / (1 - ((n : ℝ) / N) ^ 2) ^ 2

def actualTailGram {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.gram ℂ (sourceTailFamily hc N n)

/-- Cutoff/radius conditions precede all vectors. The complete infinite tail is
compared multiplicatively, without dividing by head energy or vector mass. -/
theorem actual_full336_all_vector {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)
    (N : ℕ) (hN9 : 9 ≤ N) (hR : |(n : ℝ)| < (N : ℝ)) :
    ∀ x : Fin 3 → ℂ,
      lower336 c N * finiteForm (Real.pi / 4) (mean c)
          (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x ≤
        Real.pi ^ 2 * N * (star x ⬝ᵥ (actualTailGram hc n N *ᵥ x)).re ∧
      Real.pi ^ 2 * N * (star x ⬝ᵥ (actualTailGram hc n N *ᵥ x)).re ≤
        upper336 c N n * finiteForm (Real.pi / 4) (mean c)
          (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x := by
  intro x
  have hN : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let v := sourceHead n x
  let A := reciprocalPolynomial 3 N (P c (threeNodes n) v)
  let B := reciprocalPolynomial 3 N (Q (threeNodes n) v)
  let dN : ℝ := (1 - ((n : ℝ) / N) ^ 2) ^ 2
  have hdN : 0 < dN := (symmetric_factor_bounds hNr hR (lt_add_one (N : ℝ))).1
  have hpair := ActualExplicit336.actual_paired_symbol_bounds_explicit336
    hc (by norm_num : 1 ≤ 3) (by norm_num; exact hN9) A B
    (reciprocalPolynomial_degree (by norm_num) _) (reciprocalPolynomial_degree (by norm_num) _)
  have heps : (3 : ℝ) ^ 2 *
      (336 * (c : ℝ) ^ 2 * (1 + Real.log (c : ℝ)) ^ 3) / N = delta336 c / N := by
    unfold delta336
    ring
  dsimp only at hpair
  rw [heps] at hpair
  have hcol : Summable (pairedColumnTerm c N (threeNodes n) v) :=
    ActualThreeNodeSourceHeadBridge.actual_tail_summable_all hc (threeNodes n)
      (by simp [threeNodes]) N v
  have hpoint (j : ℕ) : pairedTerm c N A B j ≤
        Real.pi ^ 2 * pairedColumnTerm c N (threeNodes n) v j ∧
      Real.pi ^ 2 * pairedColumnTerm c N (threeNodes n) v j ≤ pairedTerm c N A B j / dN := by
    have hNm : (N : ℝ) < (N + j + 1 : ℕ) := by
      exact_mod_cast (show N < N + j + 1 by omega)
    have hbounds := symmetric_factor_bounds hNr hR hNm
    have he := actual_pair_symmetric_denominator hn c N hN hR v j
    change Real.pi ^ 2 * (1 - ((n : ℝ) / (N + j + 1 : ℕ)) ^ 2) ^ 2 *
      pairedColumnTerm c N (threeNodes n) v j = pairedTerm c N A B j at he
    have hnon : 0 ≤ Real.pi ^ 2 * pairedColumnTerm c N (threeNodes n) v j := by
      unfold pairedColumnTerm
      positivity
    constructor
    · have hh := mul_le_mul_of_nonneg_right hbounds.2.2 hnon
      nlinarith only [he, hh]
    · apply (le_div_iff₀ hdN).mpr
      have hh := mul_le_mul_of_nonneg_right hbounds.2.1 hnon
      nlinarith only [he, hh]
  have hsumlo : (∑' j : ℕ, pairedTerm c N A B j) ≤
      Real.pi ^ 2 * (∑' j : ℕ, pairedColumnTerm c N (threeNodes n) v j) := by
    rw [← hcol.tsum_mul_left (Real.pi ^ 2)]
    exact hpair.1.tsum_le_tsum (fun j => (hpoint j).1) (hcol.mul_left _)
  have hsumhi : Real.pi ^ 2 * (∑' j : ℕ, pairedColumnTerm c N (threeNodes n) v j) ≤
      (∑' j : ℕ, pairedTerm c N A B j) / dN := by
    rw [← hcol.tsum_mul_left (Real.pi ^ 2), ← tsum_div_const]
    exact (hcol.mul_left _).tsum_le_tsum (fun j => (hpoint j).2) (hpair.1.div_const dN)
  have hH : pairedEnergy c A B = finiteForm (Real.pi / 4) (mean c)
      (arithmeticBoundarySymbol c n) ((n : ℝ) / N) x := actual_finite_energy_form hn c N hN x
  have hlow : lower336 c N * pairedEnergy c A B ≤
      (∑' j : ℕ, pairedTerm c N A B j) * N := by
    have hh := (div_le_iff₀ hNr).mp hpair.2.1
    simpa only [lower336] using hh
  have hupp : (∑' j : ℕ, pairedTerm c N A B j) * N ≤
      (1 + delta336 c / N) * pairedEnergy c A B := by
    have hh := (le_div_iff₀ hNr).mp hpair.2.2
    exact hh
  have hK : (star x ⬝ᵥ (actualTailGram hc n N *ᵥ x)).re =
      ∑' j : ℕ, pairedColumnTerm c N (threeNodes n) v j := by
    have hh := congrArg Complex.re (actual_source_gram_tsum hc n N x)
    simpa only [actualTailGram, Complex.ofReal_re] using hh
  simp only [hK, ← hH]
  constructor
  · exact hlow.trans (by nlinarith only [mul_le_mul_of_nonneg_right hsumlo hNr.le])
  · calc
      Real.pi ^ 2 * N * (∑' j : ℕ, pairedColumnTerm c N (threeNodes n) v j) =
          (Real.pi ^ 2 * (∑' j : ℕ, pairedColumnTerm c N (threeNodes n) v j)) * N := by ring
      _ ≤ ((∑' j : ℕ, pairedTerm c N A B j) / dN) * N :=
        mul_le_mul_of_nonneg_right hsumhi hNr.le
      _ = ((∑' j : ℕ, pairedTerm c N A B j) * N) / dN := by ring
      _ ≤ ((1 + delta336 c / N) * pairedEnergy c A B) / dN :=
        div_le_div_of_nonneg_right hupp hdN.le
      _ = upper336 c N n * pairedEnergy c A B := by dsimp [upper336, dN]; ring

theorem actual_full336_loewner {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)
    (N : ℕ) (hN9 : 9 ≤ N) (hR : |(n : ℝ)| < (N : ℝ)) :
    let H := finiteMatrix (Real.pi / 4) (mean c)
      (arithmeticBoundarySymbol c n) ((n : ℝ) / N)
    let K := actualTailGram hc n N
    ((((Real.pi ^ 2 * N : ℝ) : ℂ) • K) - ((lower336 c N : ℂ) • H)).PosSemidef ∧
      (((upper336 c N n : ℂ) • H) - (((Real.pi ^ 2 * N : ℝ) : ℂ) • K)).PosSemidef := by
  dsimp only
  have hK : (actualTailGram hc n N).IsHermitian := Matrix.isHermitian_gram _ _
  have hH := finiteMatrix_isHermitian (Real.pi / 4) (mean c)
    (arithmeticBoundarySymbol c n) ((n : ℝ) / N)
  have hreal (q : ℝ) : IsSelfAdjoint (q : ℂ) := by
    change star (q : ℂ) = (q : ℂ)
    simp
  have hsource (x : Fin 3 → ℂ) :
      star x ⬝ᵥ (actualTailGram hc n N *ᵥ x) =
        ((∑' j : ℕ, pairedColumnTerm c N (threeNodes n) (sourceHead n x) j : ℝ) : ℂ) :=
    actual_source_gram_tsum hc n N x
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((hK.smul (hreal _)).sub (hH.smul (hreal _)))
    intro x
    simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, hsource, finiteMatrix_form]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    apply Complex.ofReal_nonneg
    have hh := (actual_full336_all_vector hc hn N hN9 hR x).1
    rw [hsource x] at hh
    simpa only [Complex.ofReal_re] using sub_nonneg.mpr hh
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((hH.smul (hreal _)).sub (hK.smul (hreal _)))
    intro x
    simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, hsource, finiteMatrix_form]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    apply Complex.ofReal_nonneg
    have hh := (actual_full336_all_vector hc hn N hN9 hR x).2
    rw [hsource x] at hh
    simpa only [Complex.ofReal_re] using sub_nonneg.mpr hh

end D5.S3.Weil.ZetaBridge.ActualThreeNodeFull336
