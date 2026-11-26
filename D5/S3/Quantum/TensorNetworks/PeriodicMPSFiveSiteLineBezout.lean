/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteLineBezout
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteLineBezout
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.OfFn]
   utility: none
   digest: Modular Bézout identity for the five-site critical-minor line restrictions. -/
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! The two residue-field restrictions share no projective root. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteLineBezout

open Polynomial

abbrev F := ZMod 1009

private def first : Fin 76 → F :=
  ![758, 26, 392, 816, 622, 295, 284, 368, 960, 641, 547, 766,
    28, 174, 85, 830, 480, 619, 834, 195, 555, 977, 232, 130,
    76, 762, 149, 396, 160, 28, 383, 297, 814, 4, 353, 621,
    386, 181, 960, 693, 174, 208, 412, 967, 444, 623, 939, 20,
    207, 743, 517, 123, 796, 585, 405, 865, 656, 946, 243, 653,
    216, 128, 673, 662, 551, 211, 50, 252, 857, 118, 885, 509,
    596, 340, 52, 266]

private def second : Fin 76 → F :=
  ![385, 689, 121, 822, 127, 889, 983, 694, 674, 370, 218, 814,
    32, 98, 65, 672, 168, 355, 662, 668, 628, 838, 1000, 188,
    635, 797, 438, 864, 65, 43, 298, 995, 994, 660, 575, 591,
    902, 765, 69, 80, 812, 599, 831, 1000, 73, 644, 661, 806,
    913, 148, 526, 669, 658, 954, 174, 732, 711, 32, 488, 77,
    65, 541, 154, 716, 436, 780, 669, 161, 914, 364, 32, 106,
    857, 557, 238, 790]

private def leftMultiplier : Fin 76 → F :=
  ![255, 527, 446, 853, 754, 494, 250, 708, 132, 75, 127, 613,
    549, 438, 989, 963, 906, 533, 293, 962, 509, 98, 823, 922,
    337, 746, 749, 957, 879, 244, 474, 522, 602, 824, 433, 825,
    334, 330, 487, 372, 178, 630, 163, 184, 437, 682, 636, 127,
    601, 700, 566, 435, 855, 814, 569, 612, 822, 412, 249, 712,
    554, 838, 490, 765, 86, 600, 52, 30, 573, 723, 955, 401,
    713, 605, 178, 0]

private def rightMultiplier : Fin 76 → F :=
  ![942, 918, 1005, 870, 668, 433, 428, 901, 70, 259, 323, 286,
    850, 315, 663, 475, 915, 145, 935, 671, 555, 693, 501, 335,
    350, 416, 808, 756, 571, 896, 413, 99, 576, 582, 256, 966,
    195, 910, 905, 269, 700, 231, 447, 815, 855, 524, 526, 18,
    401, 543, 40, 345, 248, 39, 779, 108, 875, 754, 20, 328,
    433, 657, 715, 226, 922, 390, 13, 526, 400, 619, 657, 517,
    288, 515, 594, 0]

private def extendZero (a : Fin 76 → F) (n : ℕ) : F :=
  if h : n < 76 then a ⟨n, h⟩ else 0

private lemma coeff_ofFn (a : Fin 76 → F) (n : ℕ) :
    (ofFn 76 a).coeff n = extendZero a n := by
  unfold extendZero
  split
  · exact ofFn_coeff_eq_val_of_lt _ ‹n < 76›
  · exact ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_lt ‹¬ n < 76›)

private def convolution (a b : Fin 76 → F) (n : ℕ) : F :=
  ∑ i ∈ Finset.range (n+1), extendZero a i * extendZero b (n-i)

private lemma coeff_product (a b : Fin 76 → F) (n : ℕ) :
    (ofFn 76 a * ofFn 76 b).coeff n = convolution a b n := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [convolution, coeff_ofFn]

private lemma convolution_high (a b : Fin 76 → F) (n : ℕ) (hn : 150 < n) :
    convolution a b n = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hin := Finset.mem_range.mp hi
  unfold extendZero
  split
  · rw [dite_eq_right (show ¬ n-i < 76 by omega), mul_zero]
  · simp

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Each of the 151 summation identities is checked separately by kernel reduction.
private lemma coefficient_identity (n : Fin 151) :
    convolution leftMultiplier first n + convolution rightMultiplier second n =
      if (n : ℕ) = 0 then 1 else 0 := by
  fin_cases n <;> decide +kernel

/-- First degree-75 residual line polynomial of the five-site critical minors. -/
def firstPolynomial : F[X] := ofFn 76 first

/-- Second degree-75 residual line polynomial of the five-site critical minors. -/
def secondPolynomial : F[X] := ofFn 76 second

/-- The modular restrictions have an explicit polynomial Bézout identity. -/
theorem coprime_line_restrictions : IsCoprime firstPolynomial secondPolynomial := by
  refine ⟨ofFn 76 leftMultiplier, ofFn 76 rightMultiplier, ?_⟩
  ext n
  rw [Polynomial.coeff_add, firstPolynomial, secondPolynomial, coeff_product, coeff_product,
    Polynomial.coeff_one]
  by_cases hn : n < 151
  · exact coefficient_identity ⟨n, hn⟩
  · have hn' : 150 < n := by omega
    simp [convolution_high _ _ _ hn', show n ≠ 0 by omega]

/-- The point evaluation of the first certified coefficient vector. -/
def firstValue (x : F) : F := ∑ i : Fin 76, first i * x ^ (i : ℕ)

/-- The point evaluation of the second certified coefficient vector. -/
def secondValue (x : F) : F := ∑ i : Fin 76, second i * x ^ (i : ℕ)

theorem first_eval (x : F) : firstPolynomial.eval x = firstValue x := by
  simp [firstPolynomial, firstValue, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem second_eval (x : F) : secondPolynomial.eval x = secondValue x := by
  simp [secondPolynomial, secondValue, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem first_natDegree : firstPolynomial.natDegree = 75 := by
  apply le_antisymm (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) first))
  apply le_natDegree_of_ne_zero
  change (ofFn 76 first).coeff 75 ≠ 0
  rw [ofFn_coeff_eq_val_of_lt first (show 75 < 76 by decide)]
  decide +kernel

theorem second_natDegree : secondPolynomial.natDegree = 75 := by
  apply le_antisymm (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) second))
  apply le_natDegree_of_ne_zero
  change (ofFn 76 second).coeff 75 ≠ 0
  rw [ofFn_coeff_eq_val_of_lt second (show 75 < 76 by decide)]
  decide +kernel

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteLineBezout
