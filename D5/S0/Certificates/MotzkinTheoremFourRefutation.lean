/- GID: D5/S0/Certificates/MotzkinTheoremFourRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/MotzkinTheoremFourRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block, mathlib/module/Mathlib.Tactic.IntervalCases, mathlib/module/Mathlib.Tactic.NormNum]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/MotzkinTheoremFourRefutation.claim; result=D5/S0/Certificates/MotzkinTheoremFourRefutation.result; claim=D5/S0/Certificates/MotzkinTheoremFourRefutation.claim
   digest: Refutes only the printed H_{12n+7}=-64(n+1)^2 clause of Theorem 4, arXiv:2502.21050v1, at n=0; 11/12 controls support a typographical sign error; literature-attested via section 3.2, equation (6) and its initial values. 本模块不主张作者的意图命题为假，也不主张其证明有洞。 -/

import D5.S0.Certificates.MotzkinConvolutionHankelRefutation
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S0.Certificates.MotzkinTheoremFourRefutation

open D5.S0.Certificates.MotzkinConvolutionHankelRefutation (motzkin convolutionPower hankel)
open scoped BigOperators

/-!
Wang--Zhang, *Hankel determinants for convolution powers of Motzkin numbers*,
https://arxiv.org/html/2502.21050v1#Thmthm4, printed page 3:
`H_{12n+7}(F(x,4)) = H_{12n+10}(F(x,4)) = -64(n+1)^2`.
The statement has no restriction on n. The claim below isolates its H_{12n+7}
subclause. The witness n=0 has H_7=+64; H_10=-64 also makes the printed equality
between them fail. Only the H_7 obstruction is needed by the kernel proof.

Two independently coded exact computations (Bareiss and rational Gaussian
elimination, with independently generated coefficients) give these controls:

index       0  1   2    3   4   5   6    7  8  9   10   11
printed     1  1  -2  -18  -1  -1  20  -64  0  0  -64  -44
Bareiss     1  1  -2  -18  -1  -1  20   64  0  0  -64  -44
Gaussian    1  1  -2  -18  -1  -1  20   64  0  0  -64  -44

This 11/12 agreement strongly suggests a typographical sign error, with
`+64(n+1)^2` a candidate correction for the H_{12n+7} subclause. This module
does not prove that corrected formula for all n or audit the paper's proof.
本模块不主张作者的意图命题为假，也不主张其证明有洞。

Literature status: literature-attested (searched 2026-09-10, Asia/Singapore).
The SAME paper, section 3.2, equation (6), gives
`H_{12n+j+1}(F) = H_j(F_1^{(n+1)})`; its subsequent initial-value table gives
`H_6(F_1^{n+1}) = +64(n+1)^2` and `H_9(F_1^{n+1}) = -64(n+1)^2`.
Thus the correct numerical sign is already supported by the literature;
this is not a priority claim or an assertion that a separate erratum exists.
The arXiv history lists only v1. DuckDuckGo title/erratum searches and Crossref
title results did not locate a separate correction. The citing paper
https://arxiv.org/html/2503.17187, section 3.2 and reference 24, was checked
and does not identify this error. These are bounded search findings.

Only claim and result are included. All finite evidence is proof-local.
Admission basis: escape-witness, form (2). Fresh coefficient and matrix
computations produce the numerical obstruction on result's live proof path;
no frozen numerical theorem supplies H_7. The definitions are imported intact.
-/

/-- Exactly the printed H_{12n+7} subclause, universally quantified including
n=0. The other eleven residue values are not asserted by this definition. -/
def claim : Prop :=
  ∀ n : ℕ, hankel (convolutionPower 4) (12 * n + 7) =
    (-64 : ℤ) * ((n : ℤ) + 1) ^ 2

set_option maxHeartbeats 2000000 in
-- The allowance covers finite coefficient sums and the integer matrix certificate.
/-- A kernel-checked certificate gives H_7=64, contradicting the printed
subclause's value -64 at n=0. No finite instance is exported separately. -/
theorem result : ¬ claim := by
  intro h
  have power_zero (n : ℕ) :
      convolutionPower 0 n = if n = 0 then 1 else 0 := rfl
  have catalan_value_4 : catalan 4 = 14 := by decide +kernel
  have catalan_value_5 : catalan 5 = 42 := by decide +kernel
  have catalan_value_6 : catalan 6 = 132 := by decide +kernel
  have motzkin_values (n : ℕ) (hn : n < 13) :
      motzkin n = ([1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188, 5798, 15511] :
        List ℤ).getD n 0 := by
    interval_cases n <;>
      norm_num [motzkin, Finset.sum_range_succ, Nat.choose, catalan_two, catalan_three,
        catalan_value_4, catalan_value_5, catalan_value_6]
  have power_1_values (n : ℕ) (hn : n < 13) :
      convolutionPower 1 n = ([1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188, 5798,
        15511] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 0 k * motzkin (n - k)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_zero, motzkin_values]
  have power_2_values (n : ℕ) (hn : n < 13) :
      convolutionPower 2 n = ([1, 2, 5, 12, 30, 76, 196, 512, 1353, 3610, 9713,
        26324, 71799] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 1 k * motzkin (n - k)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_1_values, motzkin_values]
  have power_3_values (n : ℕ) (hn : n < 13) :
      convolutionPower 3 n = ([1, 3, 9, 25, 69, 189, 518, 1422, 3915, 10813, 29964,
        83304, 232323] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 2 k * motzkin (n - k)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_2_values, motzkin_values]
  have power_4_values (n : ℕ) (hn : n < 13) :
      convolutionPower 4 n = ([1, 4, 14, 44, 133, 392, 1140, 3288, 9438, 27016,
        77220, 220584, 630084] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 3 k * motzkin (n - k)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_3_values, motzkin_values]
  -- Fresh fraction-free elimination data, checked as an integer identity below.
  let sample : Matrix (Fin 7) (Fin 7) ℤ :=
    fun i j => ([1, 4, 14, 44, 133, 392, 1140, 3288, 9438, 27016, 77220, 220584,
      630084] : List ℤ).getD (i.val + j.val) 0
  let lower : Matrix (Fin 7) (Fin 7) ℤ :=
    !![1, 0, 0, 0, 0, 0, 0;
      -4, 1, 0, 0, 0, 0, 0;
      -20, 12, -2, 0, 0, 0, 0;
      -76, -21, 68, -18, 0, 0, 0;
      1, -4, -2, 4, -1, 0, 0;
      72, 38, -64, 0, 8, -1, 0;
      176, 464, -472, -320, 464, -168, 20]
  let upper : Matrix (Fin 7) (Fin 7) ℤ :=
    !![1, 4, 14, 44, 133, 392, 1140;
      0, -2, -12, -43, -140, -428, -1272;
      0, 0, -18, -68, -236, -736, -2220;
      0, 0, 0, -1, -4, -32, -192;
      0, 0, 0, 0, -1, -8, -44;
      0, 0, 0, 0, 0, 20, 168;
      0, 0, 0, 0, 0, 0, 64]
  have hankel_matrix : (fun i j : Fin 7 => convolutionPower 4 (i.val + j.val)) =
      sample := by
    funext i j
    exact power_4_values (i.val + j.val) (by omega)
  have lower_times_sample : lower * sample = upper := by
    dsimp only [lower, sample, upper]
    decide +kernel
  have lower_triangular : lower.IsLowerTriangular := by
    dsimp only [lower]
    decide +kernel
  have upper_triangular : upper.IsUpperTriangular := by
    dsimp only [upper]
    decide +kernel
  have det_lower : Matrix.det lower = (720 : ℤ) := by
    rw [Matrix.det_of_isLowerTriangular lower lower_triangular]
    dsimp only [lower]
    decide +kernel
  have det_upper : Matrix.det upper = (46080 : ℤ) := by
    rw [Matrix.det_of_isUpperTriangular upper_triangular]
    dsimp only [upper]
    decide +kernel
  have determinants := Matrix.det_mul lower sample
  rw [lower_times_sample, det_lower, det_upper] at determinants
  have hankel_seven_eq_pos64 : hankel (convolutionPower 4) 7 = 64 := by
    change Matrix.det (fun i j : Fin 7 => convolutionPower 4 (i.val + j.val)) = 64
    rw [hankel_matrix]
    omega
  have required := h 0
  change hankel (convolutionPower 4) 7 = (-64 : ℤ) * 1 ^ 2 at required
  rw [hankel_seven_eq_pos64] at required
  norm_num at required

#print axioms claim
#print axioms result

end D5.S0.Certificates.MotzkinTheoremFourRefutation
