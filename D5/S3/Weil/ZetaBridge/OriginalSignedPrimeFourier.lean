/- GID: D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier
   mirror-E: none(waiver:complex-finite-Ioc-prime-integral)
   anchors: []
   utility: none
   digest: The actual signed finite prime action on arbitrary finite signed complex Fourier heads. -/

import D5.S3.Weil.ZetaBridge.OriginalSignedCompressedFourier
import D5.S3.Weil.ZetaBridge.OriginalSignedPrimeBound
import Mathlib.Tactic

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

/-- An arbitrary finite signed set, with arbitrary complex coefficients. -/
def head (L : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ S, v n * mode L n x

private lemma head_continuous (L : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) :
    Continuous (head L S v) := by
  unfold head
  exact continuous_finset_sum _ fun n _ => continuous_const.mul (mode_continuous L n)

private lemma head_pairing (L s : ℝ) (S : Finset ℤ) (v : ℤ → ℂ) :
    pairing (L / 2) s (fun x => conj (head L S v x)) (head L S v) =
      ∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) * entry L m n (-s) := by
  have he : (fun x => conj (head L S v x)) =
      (fun x => ∑ m ∈ S, conj (v m) * conj (mode L m x)) := by
    funext x
    simp [head, map_sum, map_mul]
  rw [he]
  change pairing (L / 2) s (fun x => ∑ m ∈ S, conj (v m) * conj (mode L m x))
    (fun x => ∑ n ∈ S, v n * mode L n x) = _
  rw [pairing_finite _ _ S S (fun m => conj (v m)) v
    (fun m x => conj (mode L m x)) (mode L)
    (by intro m _; have := mode_continuous L m; fun_prop)
    (by intro n _; exact mode_continuous L n)]
  simp only [entry, neg_neg]

/-- The signed matrix is calculated from both independently compressed
translations; no desired matrix is supplied as a premise. All prime-power
rows use the existing von Mangoldt half-density weights. -/
def primeMatrix (L : ℝ) (M : ℕ) (m n : ℤ) : ℂ :=
  -∑ q ∈ Finset.Icc 1 M, (primeWeight q : ℂ) *
    (matrix L m n (Real.log (q : ℝ)) + matrix L m n (-Real.log (q : ℝ)))


/-- Full original signed complex quadratic identity, before any parity or
reality restriction. The literal cutoff and endpoint compression are reused
from the actual arithmetic owner. -/
theorem finite_signed_prime_identity (L : ℝ) (hL : 0 < L) (M : ℕ)
    (hM : primeCutoff (L / 2) ≤ M) (S : Finset ℤ) (v : ℤ → ℂ) :
    (∫ x in window (L / 2), conj (zeroExtension (L / 2) (head L S v) x) *
      (-primeSymmetric (L / 2) M (zeroExtension (L / 2) (head L S v)) x)) =
      ∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) *
        primeMatrix L (primeCutoff (L / 2)) m n := by
  have hphysical :
      (∫ x in window (L / 2), conj (zeroExtension (L / 2) (head L S v) x) *
        (-primeSymmetric (L / 2) M (zeroExtension (L / 2) (head L S v)) x)) =
        -primeQuadratic (L / 2) M (head L S v) := by
    rw [primeQuadratic_physical]
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    have hF : zeroExtension (L / 2) (head L S v) x = head L S v x :=
      Set.indicator_of_mem hx _
    dsimp only
    rw [hF, ← primeAction_existing _ M _ x hx]
    ring
  rw [hphysical]
  have hcut : primeQuadratic (L / 2) M (head L S v) =
      primeQuadratic (L / 2) (primeCutoff (L / 2)) (head L S v) := by
    unfold primeQuadratic
    rw [primeAction_cutoff _ M hM]
  rw [hcut, prime_bilinear _ _ _ (fun s =>
    integrable_compression_product _ s
      (Complex.continuous_conj.comp (head_continuous L S v)) (head_continuous L S v))]
  simp_rw [head_pairing, neg_neg, entry_eq_matrix L hL]
  have hrow (q : ℕ) :
      (primeWeight q : ℂ) *
        ((∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) * matrix L m n (-Real.log (q : ℝ))) +
          (∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) * matrix L m n (Real.log (q : ℝ)))) =
      ∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) *
        ((primeWeight q : ℂ) *
          (matrix L m n (Real.log (q : ℝ)) + matrix L m n (-Real.log (q : ℝ)))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  simp_rw [hrow, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  unfold primeMatrix
  rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]

/-- Actual integral mode bounds control every entry of the signed finite
matrix. The weights are kept inside absolute values; positivity is unused. -/
theorem primeMatrix_norm_le (L : ℝ) (hL : 0 < L) (M : ℕ) (m n : ℤ) :
    ‖primeMatrix L M m n‖ ≤ 2 * ∑ q ∈ Finset.Icc 1 M, |primeWeight q| := by
  unfold primeMatrix
  rw [norm_neg, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hp := entry_norm_le_one L hL m n (Real.log (q : ℝ))
  have hm := entry_norm_le_one L hL m n (-Real.log (q : ℝ))
  rw [entry_eq_matrix L hL] at hp hm
  have ht := norm_add_le (matrix L m n (Real.log (q : ℝ)))
    (matrix L m n (-Real.log (q : ℝ)))
  nlinarith [abs_nonneg (primeWeight q)]

/-- A finite all-complex coefficient norm bound obtained from the actual
integral estimates. It holds at every cutoff, with all prime powers retained. -/
theorem finite_signed_prime_norm_le (L : ℝ) (hL : 0 < L) (M : ℕ)
    (S : Finset ℤ) (v : ℤ → ℂ) :
    ‖∑ m ∈ S, ∑ n ∈ S, (conj (v m) * v n) * primeMatrix L M m n‖ ≤
      (2 * ∑ q ∈ Finset.Icc 1 M, |primeWeight q|) * (∑ n ∈ S, ‖v n‖) ^ 2 := by
  calc
    _ ≤ ∑ m ∈ S, ∑ n ∈ S,
        (‖v m‖ * ‖v n‖) * (2 * ∑ q ∈ Finset.Icc 1 M, |primeWeight q|) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro m _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n _
      simp only [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (primeMatrix_norm_le L hL M m n) (by positivity)
    _ = _ := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      ring

end OriginalSignedPrimeFourier
