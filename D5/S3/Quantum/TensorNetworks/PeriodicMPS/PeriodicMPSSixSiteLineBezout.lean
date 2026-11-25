/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteLineBezout
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteLineBezout
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.OfFn]
   utility: none
   digest: Modular Bézout identity for the six-site critical-minor line restrictions. -/
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! The two residue-field restrictions share no projective root. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteLineBezout

open Polynomial

abbrev F := ZMod 1009

private def first : Fin 94 → F :=
  ![67, 365, 16, 946, 647, 546, 886, 904, 633, 895, 84, 193,
    55, 838, 722, 716, 697, 767, 425, 70, 732, 537, 854, 721,
    401, 756, 254, 1003, 371, 978, 360, 857, 456, 739, 996, 307,
    479, 106, 475, 813, 342, 895, 173, 419, 207, 825, 297, 689,
    392, 256, 583, 101, 401, 414, 655, 819, 613, 118, 627, 665,
    266, 442, 638, 442, 111, 889, 111, 326, 405, 598, 997, 791,
    715, 503, 488, 192, 729, 362, 791, 969, 909, 601, 483, 691,
    532, 853, 853, 851, 535, 503, 11, 851, 642, 652]

private def second : Fin 94 → F :=
  ![419, 952, 227, 458, 117, 471, 426, 144, 161, 43, 860, 740,
    360, 677, 67, 478, 630, 470, 685, 640, 116, 842, 69, 104,
    474, 120, 593, 465, 559, 337, 373, 676, 691, 750, 307, 405,
    347, 721, 108, 351, 995, 312, 897, 383, 550, 395, 607, 542,
    494, 877, 358, 124, 398, 660, 338, 414, 660, 796, 726, 327,
    69, 814, 784, 890, 266, 31, 195, 438, 988, 825, 515, 422,
    506, 23, 581, 200, 940, 667, 230, 943, 138, 633, 460, 664,
    418, 997, 328, 477, 350, 207, 881, 447, 799, 648]

private def leftMultiplier : Fin 94 → F :=
  ![61, 420, 940, 792, 647, 34, 807, 109, 654, 343, 393, 718,
    277, 609, 714, 833, 43, 126, 571, 57, 98, 88, 865, 323,
    539, 68, 323, 911, 165, 50, 731, 744, 930, 296, 245, 157,
    531, 874, 348, 890, 678, 390, 62, 455, 224, 780, 893, 576,
    63, 195, 998, 445, 156, 291, 1003, 791, 186, 883, 169, 311,
    540, 553, 65, 568, 592, 263, 16, 438, 861, 96, 909, 555,
    690, 640, 402, 139, 121, 396, 921, 83, 104, 761, 711, 790,
    544, 439, 372, 466, 728, 619, 897, 352, 209, 0]

private def rightMultiplier : Fin 94 → F :=
  ![154, 835, 328, 268, 918, 791, 78, 38, 421, 366, 168, 513,
    1007, 821, 767, 396, 89, 987, 373, 119, 389, 896, 613, 38,
    544, 620, 852, 983, 386, 926, 699, 638, 787, 625, 1000, 910,
    224, 599, 445, 325, 451, 431, 382, 126, 401, 691, 677, 206,
    1006, 662, 900, 90, 654, 287, 825, 400, 805, 409, 963, 334,
    549, 276, 671, 838, 658, 31, 515, 340, 491, 77, 272, 338,
    275, 395, 473, 346, 69, 1001, 765, 726, 958, 195, 668, 250,
    187, 822, 625, 530, 571, 659, 790, 625, 643, 0]

private def extendZero (a : Fin 94 → F) (n : ℕ) : F :=
  if h : n < 94 then a ⟨n, h⟩ else 0

private lemma coeff_ofFn (a : Fin 94 → F) (n : ℕ) :
    (ofFn 94 a).coeff n = extendZero a n := by
  unfold extendZero
  split
  · exact ofFn_coeff_eq_val_of_lt _ ‹n < 94›
  · exact ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_lt ‹¬ n < 94›)

private def convolution (a b : Fin 94 → F) (n : ℕ) : F :=
  ∑ i ∈ Finset.range (n+1), extendZero a i * extendZero b (n-i)

private lemma coeff_product (a b : Fin 94 → F) (n : ℕ) :
    (ofFn 94 a * ofFn 94 b).coeff n = convolution a b n := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [convolution, coeff_ofFn]

private lemma convolution_high (a b : Fin 94 → F) (n : ℕ) (hn : 186 < n) :
    convolution a b n = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hin := Finset.mem_range.mp hi
  unfold extendZero
  split
  · rw [dite_eq_right (show ¬ n-i < 94 by omega), mul_zero]
  · simp

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Each of the 187 summation identities is checked separately by kernel reduction.
private lemma coefficient_identity (n : Fin 187) :
    convolution leftMultiplier first n + convolution rightMultiplier second n =
      if (n : ℕ) = 0 then 1 else 0 := by
  fin_cases n <;> decide +kernel

/-- First degree-93 residual line polynomial of the six-site critical minors. -/
def firstPolynomial : F[X] := ofFn 94 first

/-- Second degree-93 residual line polynomial of the six-site critical minors. -/
def secondPolynomial : F[X] := ofFn 94 second

/-- The modular restrictions have an explicit polynomial Bézout identity. -/
theorem coprime_line_restrictions : IsCoprime firstPolynomial secondPolynomial := by
  refine ⟨ofFn 94 leftMultiplier, ofFn 94 rightMultiplier, ?_⟩
  ext n
  rw [Polynomial.coeff_add, firstPolynomial, secondPolynomial, coeff_product, coeff_product,
    Polynomial.coeff_one]
  by_cases hn : n < 187
  · exact coefficient_identity ⟨n, hn⟩
  · have hn' : 186 < n := by omega
    simp [convolution_high _ _ _ hn', show n ≠ 0 by omega]

/-- The point evaluation of the first certified coefficient vector. -/
def firstValue (x : F) : F := ∑ i : Fin 94, first i * x ^ (i : ℕ)

/-- The point evaluation of the second certified coefficient vector. -/
def secondValue (x : F) : F := ∑ i : Fin 94, second i * x ^ (i : ℕ)

theorem first_eval (x : F) : firstPolynomial.eval x = firstValue x := by
  simp [firstPolynomial, firstValue, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem second_eval (x : F) : secondPolynomial.eval x = secondValue x := by
  simp [secondPolynomial, secondValue, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem first_natDegree : firstPolynomial.natDegree = 93 := by
  apply le_antisymm (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) first))
  apply le_natDegree_of_ne_zero
  change (ofFn 94 first).coeff 93 ≠ 0
  rw [ofFn_coeff_eq_val_of_lt first (show 93 < 94 by decide)]
  decide +kernel

theorem second_natDegree : secondPolynomial.natDegree = 93 := by
  apply le_antisymm (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) second))
  apply le_natDegree_of_ne_zero
  change (ofFn 94 second).coeff 93 ≠ 0
  rw [ofFn_coeff_eq_val_of_lt second (show 93 < 94 by decide)]
  decide +kernel

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteLineBezout
