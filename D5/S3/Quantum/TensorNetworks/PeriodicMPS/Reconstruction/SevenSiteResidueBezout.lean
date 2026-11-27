/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBezout
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBezout
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant]
   utility: none
   digest: Exact coefficient convolution gives a Bézout identity for the two quotient-table polynomials modulo 1009. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteResidueDeterminant
import Mathlib.RingTheory.Polynomial.Resultant.Basic

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

open Polynomial

theorem lineQuotient_degree (r : Fin 10) (hr : r = 0 ∨ r = 1) :
    (lineQuotient r).natDegree = 46 := by
  apply le_antisymm (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _))
  apply le_natDegree_of_ne_zero
  change (ofFn 47 (quotientCoefficients r)).coeff 46 ≠ 0
  rw [ofFn_coeff_eq_val_of_lt _ (show 46 < 47 by decide)]
  rcases hr with rfl | rfl <;> decide +kernel

private def extendZero {d : ℕ} (a : Fin d → F) (i : ℕ) : F :=
  if h : i < d then a ⟨i, h⟩ else 0

private theorem coeff_ofFn {d : ℕ} (a : Fin d → F) (i : ℕ) :
    (ofFn d a).coeff i = extendZero a i := by
  unfold extendZero
  split
  · exact ofFn_coeff_eq_val_of_lt _ ‹i < d›
  · exact ofFn_coeff_eq_zero_of_ge _ (by omega)

private def convolution {d e : ℕ} (a : Fin d → F) (b : Fin e → F) (n : ℕ) : F :=
  ∑ i ∈ Finset.range (n + 1), extendZero a i * extendZero b (n - i)

private theorem coeff_product {d e : ℕ} (a : Fin d → F) (b : Fin e → F) (n : ℕ) :
    (ofFn d a * ofFn e b).coeff n = convolution a b n := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [convolution, coeff_ofFn]

private theorem convolution_high (a : Fin 46 → F) (b : Fin 47 → F) (n : ℕ) (hn : 92 ≤ n) :
    convolution a b n = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hin := Finset.mem_range.mp hi
  unfold extendZero
  split
  · rw [dite_eq_right (show ¬ n-i < 47 by omega), mul_zero]
  · simp

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem coefficient_identity (n : Fin 92) :
    convolution bezout_0 quotient_0 n + convolution bezout_1 quotient_1 n =
      if (n : ℕ) = 0 then 1 else 0 := by
  fin_cases n <;> decide +kernel

theorem concrete_bezout :
    ofFn 46 bezout_0 * lineQuotient 0 + ofFn 46 bezout_1 * lineQuotient 1 = 1 := by
  change ofFn 46 bezout_0 * ofFn 47 quotient_0 + ofFn 46 bezout_1 * ofFn 47 quotient_1 = 1
  ext n
  rw [Polynomial.coeff_add, coeff_product, coeff_product, Polynomial.coeff_one]
  by_cases hn : n < 92
  · exact coefficient_identity ⟨n, hn⟩
  · simp [convolution_high _ _ _ (by omega : 92 ≤ n), show n ≠ 0 by omega]

theorem concrete_coprime : IsCoprime (lineQuotient 0) (lineQuotient 1) :=
  ⟨ofFn 46 bezout_0, ofFn 46 bezout_1, concrete_bezout⟩

theorem concrete_resultant : resultant (lineQuotient 0) (lineQuotient 1) ≠ 0 :=
  resultant_ne_zero _ _ concrete_coprime

end D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate
