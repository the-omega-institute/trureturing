/- GID: D5/S0/Certificates/CatalanConjectureSevenRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/CatalanConjectureSevenRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block, mathlib/module/Mathlib.Tactic.IntervalCases, mathlib/module/Mathlib.Tactic.NormNum]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/CatalanConjectureSevenRefutation.claim; result=D5/S0/Certificates/CatalanConjectureSevenRefutation.result; claim=D5/S0/Certificates/CatalanConjectureSevenRefutation.claim
   digest: Refutes only the printed last clause of Conjecture 7 in arXiv:1811.00248v2 at t=2,n=1; literature-attested, new_counterexample_claimed=false. No claim against the intended proposition or its proof, or Cigler's arXiv:1801.05608 original, whose two terms both use C^5 here; no priority claimed for the determinant values or identification of the printing error. -/

import D5.S0.Certificates.MotzkinConvolutionHankelRefutation
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S0.Certificates.CatalanConjectureSevenRefutation

open D5.S0.Certificates.MotzkinConvolutionHankelRefutation (hankel)
open scoped BigOperators

/-!
Wang--Xin, *Hankel determinants for convolution powers of Catalan numbers*,
arXiv:1811.00248v2, printed page 3, Conjecture 7, last line, reads
`H_{(2t+1)n-1}(F(x,2t+1)) + H_{(2t+1)n+2}(F(x,2t))
  = (-1)^{tn+1}(t-1)(2t+1)`.
The original PDF was visually checked, including the second argument `2t`.
The scope sentence is "For odd positive integer r = 2t+1, we have".
There is no printed lower bound on t or n. We refute its universal
positive-t part; n ranges over all naturals, with natural index subtraction.
The witness t=2,n=1 has strictly positive indices, so subtraction is exact.

The definitions on printed pages 1, 2 and 5 are the unshifted Hankel
determinant (including H_0=1), F(x,r)=C(x)^r, and C(x)=1+x*C(x)^2.
Mathlib's catalan is the latter recurrence; catalan_eq_centralBinom_div
identifies it with the source's binom(2n,n)/(n+1). We directly reuse the
frozen hankel definition and define powers by Cauchy multiplication below.

Provenance: literature-attested; new_counterexample_claimed=false.
The same paper's Theorem 2 gives H_7(C^4)=-4, and Theorem 3 gives H_4(C^5)=5.
Its reference [9] is Cigler, *Catalan numbers, Hankel determinants and
Fibonacci polynomials*, arXiv:1801.05608. That paper's v3, printed page 26,
Conjecture 7.2 (7.6), uses 2k+1 in BOTH terms. At k=2,n=1 it reads
H_4(C^5)+H_7(C^5)=-5, consistent with 5+(-10)=-5.
Only the printed 1811.00248v2 last clause is refuted at t=2,n=1.
We make no claim that the intended proposition is false or its proof has
a gap, nor that Cigler's corresponding original is false. We claim neither
first discovery of these determinant values nor first identification of
the printing error. PDF and library searches were performed on 2026-09-10.

The proof needs only Mathlib, the frozen definition, and exact computation.
The local computation establishes the numerical obstruction rather than
instantiating a previously formalized numerical determinant theorem.
Admission: escape-witness, section 3.2 form (2), on result's live path.
The finite tables and matrix certificate are proof-local; the sole public
theorem is the closed negation of claim. No numerical oracle is trusted.
-/

/-- Coefficients of C(x)^r by iterated Cauchy multiplication, with C^0=1. -/
def convolutionPower : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | r + 1, n => ∑ k ∈ Finset.range (n + 1),
      convolutionPower r k * (catalan (n - k) : ℤ)

/-- The complete printed last clause, for every positive t and every natural n.
In particular, the second power is 2t, exactly as printed, not 2t+1. -/
def claim : Prop :=
  ∀ t : ℕ, 0 < t → ∀ n : ℕ,
    hankel (convolutionPower (2 * t + 1)) ((2 * t + 1) * n - 1) +
      hankel (convolutionPower (2 * t)) ((2 * t + 1) * n + 2) =
        (-1 : ℤ) ^ (t * n + 1) * ((t : ℤ) - 1) * (2 * (t : ℤ) + 1)

set_option maxHeartbeats 4000000 in
-- The allowance covers finite coefficient normalization and the integer certificate.
/-- At t=2,n=1 the printed clause forces 1=-5. Both determinants are
kernel-checked from the definitions; the seven by seven case uses L*A=U. -/
theorem result : ¬ claim := by
  intro h
  have power_zero (n : ℕ) :
      convolutionPower 0 n = if n = 0 then 1 else 0 := rfl
  have catalan_values (n : ℕ) (hn : n < 13) :
      (catalan n : ℤ) = ([1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786,
        208012] : List ℤ).getD n 0 := by
    rw [catalan_eq_centralBinom_div, Nat.centralBinom,
      Nat.choose_eq_descFactorial_div_factorial]
    interval_cases n <;> norm_num [Nat.descFactorial, Nat.factorial]
  have power_one (n : ℕ) (hn : n < 13) :
      convolutionPower 1 n = ([1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786,
        208012] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 0 k * (catalan (n - k) : ℤ)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_zero, catalan_values]
  have power_two (n : ℕ) (hn : n < 13) :
      convolutionPower 2 n = ([1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012,
        742900] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 1 k * (catalan (n - k) : ℤ)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_one, catalan_values]
  have power_three (n : ℕ) (hn : n < 13) :
      convolutionPower 3 n = ([1, 3, 9, 28, 90, 297, 1001, 3432, 11934, 41990, 149226, 534888,
        1931540] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 2 k * (catalan (n - k) : ℤ)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_two, catalan_values]
  have power_four (n : ℕ) (hn : n < 13) :
      convolutionPower 4 n = ([1, 4, 14, 48, 165, 572, 2002, 7072, 25194, 90440, 326876,
        1188640, 4345965] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 3 k * (catalan (n - k) : ℤ)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_three, catalan_values]
  have power_five (n : ℕ) (hn : n < 7) :
      convolutionPower 5 n = ([1, 5, 20, 75, 275, 1001, 3640] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 4 k * (catalan (n - k) : ℤ)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_four, catalan_values]
  have hankel_four : hankel (convolutionPower 5) 4 = 5 := by
    have matrix_eq : (fun i j : Fin 4 => convolutionPower 5 (i.val + j.val)) =
        (fun i j : Fin 4 => ([1, 5, 20, 75, 275, 1001, 3640] : List ℤ).getD
          (i.val + j.val) 0) := by
      funext i j
      exact power_five (i.val + j.val) (by omega)
    unfold hankel
    rw [matrix_eq]
    decide +kernel
  let sample : Matrix (Fin 7) (Fin 7) ℤ :=
    fun i j => ([1, 4, 14, 48, 165, 572, 2002, 7072, 25194, 90440, 326876, 1188640,
      4345965] : List ℤ).getD (i.val + j.val) 0
  -- Untrusted integer data, checked below by the kernel as a matrix identity.
  let lower : Matrix (Fin 7) (Fin 7) ℤ :=
    !![1, 0, 0, 0, 0, 0, 0;
      -4, 1, 0, 0, 0, 0, 0;
      -2, 4, -1, 0, 0, 0, 0;
      -20, 37, -16, 2, 0, 0, 0;
      -3, 16, -20, 8, -1, 0, 0;
      -56, 238, -304, 158, -36, 3, 0;
      -4, 40, -106, 112, -54, 12, -1]
  let upper : Matrix (Fin 7) (Fin 7) ℤ :=
    !![1, 4, 14, 48, 165, 572, 2002;
      0, -2, -8, -27, -88, -286, -936;
      0, 0, -1, -8, -44, -208, -910;
      0, 0, 0, -3, -24, -130, -600;
      0, 0, 0, 0, -1, -12, -90;
      0, 0, 0, 0, 0, -4, -48;
      0, 0, 0, 0, 0, 0, -1]
  have hankel_matrix : (fun i j : Fin 7 => convolutionPower 4 (i.val + j.val)) =
      sample := by
    funext i j
    exact power_four (i.val + j.val) (by omega)
  have lower_times_sample : lower * sample = upper := by
    dsimp only [lower, sample, upper]
    decide +kernel
  have lower_triangular : lower.IsLowerTriangular := by
    dsimp only [lower]
    decide +kernel
  have upper_triangular : upper.IsUpperTriangular := by
    dsimp only [upper]
    decide +kernel
  have det_lower : Matrix.det lower = (-6 : ℤ) := by
    rw [Matrix.det_of_isLowerTriangular lower lower_triangular]
    dsimp only [lower]
    decide +kernel
  have det_upper : Matrix.det upper = (24 : ℤ) := by
    rw [Matrix.det_of_isUpperTriangular upper_triangular]
    dsimp only [upper]
    decide +kernel
  have determinants := Matrix.det_mul lower sample
  rw [lower_times_sample, det_lower, det_upper] at determinants
  have hankel_seven : hankel (convolutionPower 4) 7 = -4 := by
    unfold hankel
    rw [hankel_matrix]
    omega
  have required := h 2 (by decide) 1
  change hankel (convolutionPower 5) 4 + hankel (convolutionPower 4) 7 =
    (-1 : ℤ) ^ 3 * (2 - 1) * (2 * 2 + 1) at required
  rw [hankel_four, hankel_seven] at required
  norm_num at required

#print axioms claim
#print axioms result

end D5.S0.Certificates.CatalanConjectureSevenRefutation
