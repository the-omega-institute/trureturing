/- GID: D5/S3/Weil/ZetaBridge/OriginalSignedPrimeArithmetic
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/OriginalSignedPrimeArithmetic
   mirror-E: none(waiver:complex-Ioc-weighted-translation)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Weil/ZetaBridge/OriginalSignedPrimeBound.original_prime80; instance=D5/S3/Weil/ZetaBridge/OriginalSignedPrimeBound.original_prime80
   digest: Original 717 rows and variable-certificate von Mangoldt and logarithm interpretation. -/

import D5.S3.Weil.ZetaBridge.OriginalSignedPrimeCellBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Factorization.PrimePow

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace OriginalSignedPrimeFourier

open MeasureTheory Set
open scoped BigOperators ComplexConjugate
open PhysicalCompressedCosineMatrix
open OriginalSignedCompressedFourier
open D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition (primeWeight)
open D5.S3.Weil.ZetaBridge.WeilMellinPrimeIntertwining (primeSymmetric)

namespace Prime80


private def logUpper (p : ℕ) : ℚ :=
  (p.log2 : ℚ) * (6931471808 / 10000000000) +
    (p : ℚ) / (2 : ℚ) ^ p.log2 - 1

/-- Numerical premises for a variable arithmetic table. Support is checked
on every Fin 5041 value; no prime-power completeness assumption is hidden. -/
structure ArithmeticCertificate (ts : List Row) : Prop where
  row_valid : ∀ t ∈ ts,
    2 ≤ t.q ∧ t.q < 5040 ∧ 0 < t.a ∧ t.a ≤ t.b ∧
      t.p.Prime ∧ 0 < t.k ∧ t.q = t.p ^ t.k
  nodup : (ts.map Row.q).Nodup
  log_ceilings : ∀ t ∈ ts,
    logUpper t.p / (t.q : ℚ) ≤ (t.a : ℚ) / 1000000 ∧
      logUpper t.p ≤ (t.b : ℚ) / 1000000
  full_support : ∀ n : Fin 5041,
    n.val.primeFactors.card = 1 ↔ n.val ∈ ts.map Row.q

variable {ts : List Row}

lemma row_of_mem (cert : ArithmeticCertificate ts) {t : Row} (ht : t ∈ ts) :
    2 ≤ t.q ∧ t.q < 5040 ∧ 0 < t.a ∧ t.a ≤ t.b ∧
      t.p.Prime ∧ 0 < t.k ∧ t.q = t.p ^ t.k := cert.row_valid t ht

lemma weight_row (cert : ArithmeticCertificate ts) (t : Row) (ht : t ∈ ts) :
    primeWeight t.q = Real.log (t.p : ℝ) / Real.sqrt (t.q : ℝ) := by
  have hp := (row_of_mem cert ht).2.2.2.2.1
  have hk := (row_of_mem cert ht).2.2.2.2.2.1
  have hq := (row_of_mem cert ht).2.2.2.2.2.2
  unfold primeWeight
  rw [hq, ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt hk),
    ArithmeticFunction.vonMangoldt_apply_prime hp]

lemma weight_zero_of_missing (cert : ArithmeticCertificate ts) {q : ℕ} (hq : q < 5041)
    (hmiss : q ∉ ts.map Row.q) : primeWeight q = 0 := by
  have hn : ¬IsPrimePow q := by
    rw [isPrimePow_iff_card_primeFactors_eq_one]
    exact fun h => hmiss ((cert.full_support ⟨q, hq⟩).mp h)
  unfold primeWeight
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div]

private lemma log_le_upper {p : ℕ} (hp : 0 < p) :
    Real.log (p : ℝ) ≤ (logUpper p : ℝ) := by
  let e := p.log2
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hd : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos hp' hd)
  rw [Real.log_div hp'.ne' hd.ne', Real.log_pow] at hl
  have htwo : Real.log 2 ≤ (6931471808 : ℝ) / 10000000000 := by
    convert Real.log_two_lt_d9.le using 1 <;> norm_num
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hm := mul_le_mul_of_nonneg_left htwo he
  have heq : (logUpper p : ℝ) =
      (e : ℝ) * ((6931471808 : ℝ) / 10000000000) +
        (p : ℝ) / (2 : ℝ) ^ e - 1 := by
    simp [logUpper, e]
  rw [heq]
  linarith

lemma row_log_bounds (cert : ArithmeticCertificate ts) (t : Row) (ht : t ∈ ts) :
    Real.log (t.p : ℝ) / (t.q : ℝ) ≤ (t.a : ℝ) / 1000000 ∧
      Real.log (t.p : ℝ) ≤ (t.b : ℝ) / 1000000 := by
  have hr := row_of_mem cert ht
  have hlog := log_le_upper hr.2.2.2.2.1.pos
  have hq : (0 : ℝ) < t.q := by exact_mod_cast (by omega : 0 < t.q)
  have hb := cert.log_ceilings t ht
  have ha' : (logUpper t.p : ℝ) / (t.q : ℝ) ≤ (t.a : ℝ) / 1000000 := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hb.1
  have hb' : (logUpper t.p : ℝ) ≤ (t.b : ℝ) / 1000000 := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hb.2
  exact ⟨(div_le_div_of_nonneg_right hlog hq.le).trans ha', hlog.trans hb'⟩

end Prime80
end OriginalSignedPrimeFourier
