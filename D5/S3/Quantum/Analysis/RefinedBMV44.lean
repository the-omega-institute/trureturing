/- GID: D5/S3/Quantum/Analysis/RefinedBMV44
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV44
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The arbitrary-dimensional refined BMV lower bounds with four copies of each factor. -/

import D5.S3.Quantum.Analysis.RefinedBMV43
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Tactic.NoncommRing

/-! # The refined BMV (4,4) product and exponential comparisons

The proof combines cyclic word counts with the fourth moment of the Hermitian
part of the product. The resulting identity splits the trace gap into terms
controlled by Frobenius squares and unitary triangularization.
-/

open Matrix

noncomputable section

namespace RefinedBMV.Algebra44

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real part of the matrix trace. -/
def realTrace (X : Matrix n n ℂ) : ℝ := (trace X).re

/-- The sum of the real traces of all words with four copies of each factor. -/
def W (A B : Matrix n n ℂ) : ℝ :=
  ((balancedWords 4 4).map fun w ↦ realTrace (evalWord A B w)).sum

def U (A B : Matrix n n ℂ) : ℝ := realTrace (A ^ 4 * B ^ 4)
def C (A B : Matrix n n ℂ) : ℝ := realTrace (A ^ 3 * B ^ 3 * A * B)
def P (A B : Matrix n n ℂ) : ℝ := realTrace (A ^ 3 * B ^ 2 * A * B ^ 2)
def Q (A B : Matrix n n ℂ) : ℝ := realTrace (A ^ 2 * B ^ 3 * A ^ 2 * B)
def J (A B : Matrix n n ℂ) : ℝ := realTrace ((A * B)ᴴ * (A * B) ^ 3)
def F (A B : Matrix n n ℂ) : ℝ := realTrace (((A * B) ^ 2)ᴴ * (A * B) ^ 2)
def S (A B : Matrix n n ℂ) : ℝ := realTrace ((A ^ 2 * B ^ 2) ^ 2)
def T (A B : Matrix n n ℂ) : ℝ := realTrace ((A * B) ^ 4)
def H (A B : Matrix n n ℂ) : ℝ := realTrace (((1 / 2 : ℝ) • (A * B + (A * B)ᴴ)) ^ 4)
def Z (A B : Matrix n n ℂ) : Matrix n n ℂ := A ^ 2 * B ^ 2 + (A * B) ^ 2
def R (A B : Matrix n n ℂ) : ℝ := realTrace ((Z A B)ᴴ * Z A B) - realTrace ((Z A B) ^ 2)

omit [DecidableEq n] in
private theorem realTrace_add (X Y : Matrix n n ℂ) :
    realTrace (X + Y) = realTrace X + realTrace Y := by
  simp only [realTrace, trace_add, Complex.add_re]

omit [DecidableEq n] in
private theorem realTrace_adjoint (X : Matrix n n ℂ) : realTrace Xᴴ = realTrace X := by
  rw [realTrace, trace_conjTranspose]
  rfl

omit [DecidableEq n] in
private theorem realTrace_mul_comm (X Y : Matrix n n ℂ) :
    realTrace (X * Y) = realTrace (Y * X) :=
  congrArg Complex.re (trace_mul_comm X Y)

local notation "𝔞" => true
local notation "𝔟" => false

private def wordU : List Bool := [𝔞, 𝔞, 𝔞, 𝔞, 𝔟, 𝔟, 𝔟, 𝔟]
private def wordC : List Bool := [𝔞, 𝔞, 𝔞, 𝔟, 𝔟, 𝔟, 𝔞, 𝔟]
private def wordP : List Bool := [𝔞, 𝔞, 𝔞, 𝔟, 𝔟, 𝔞, 𝔟, 𝔟]
private def wordQ : List Bool := [𝔞, 𝔞, 𝔟, 𝔟, 𝔟, 𝔞, 𝔞, 𝔟]
private def wordJ : List Bool := [𝔟, 𝔞, 𝔞, 𝔟, 𝔞, 𝔟, 𝔞, 𝔟]
private def wordF : List Bool := [𝔟, 𝔞, 𝔟, 𝔞, 𝔞, 𝔟, 𝔞, 𝔟]
private def wordS : List Bool := [𝔞, 𝔞, 𝔟, 𝔟, 𝔞, 𝔞, 𝔟, 𝔟]
private def wordT : List Bool := [𝔞, 𝔟, 𝔞, 𝔟, 𝔞, 𝔟, 𝔞, 𝔟]

private def rotations (w : List Bool) (period : ℕ) : List (List Bool) :=
  (List.range period).map w.rotate

private theorem balancedWords44_perm :
    (balancedWords 4 4).Perm
      (rotations wordU 8 ++ (rotations wordC 8 ++ rotations wordC.reverse 8) ++
        rotations wordP 8 ++ rotations wordQ 8 ++
        (rotations wordJ 8 ++ rotations wordJ.reverse 8) ++
        rotations wordF 8 ++ rotations wordS 4 ++ rotations wordT 2) := by
  simp only [balancedWords, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

private theorem evalWord_snoc (A B : Matrix n n ℂ) (w : List Bool) (b : Bool) :
    evalWord A B (w ++ [b]) = evalWord A B w * (if b then A else B) := by
  induction w with
  | nil => cases b <;> simp [evalWord]
  | cons a w ih => cases a <;> simp [evalWord, ih, mul_assoc]

private theorem evalWord_reverse (A B : Matrix n n ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (w : List Bool) :
    evalWord A B w.reverse = (evalWord A B w)ᴴ := by
  induction w with
  | nil => simp [evalWord]
  | cons b w ih =>
    cases b <;>
      simp [List.reverse_cons, evalWord_snoc, evalWord, ih, conjTranspose_mul, hA.eq, hB.eq]

private theorem sum_rotations (A B : Matrix n n ℂ) (w : List Bool) (period : ℕ) :
    ((rotations w period).map fun v ↦ realTrace (evalWord A B v)).sum =
      (period : ℝ) * realTrace (evalWord A B w) := by
  simp [rotations, Function.comp_def, realTrace, evalWord_rotate_trace43,
    List.map_const', List.sum_replicate, nsmul_eq_mul]

/-- The 70 word traces group into eight classes under rotations and adjunction. -/
private theorem word_enumeration (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    W A B = 8 * U A B + 16 * C A B + 8 * P A B + 8 * Q A B +
      16 * J A B + 8 * F A B + 4 * S A B + 2 * T A B := by
  unfold W
  rw [(balancedWords44_perm.map fun w ↦ realTrace (evalWord A B w)).sum_eq]
  simp only [List.map_append, List.sum_append, sum_rotations, evalWord_reverse A B hA hB,
    realTrace_adjoint]
  simp only [wordU, wordC, wordP, wordQ, wordJ, wordF, wordS, wordT, evalWord,
    U, C, P, Q, J, F, S, T, conjTranspose_mul, hA.eq, hB.eq,
    pow_succ, pow_zero, one_mul, mul_one, mul_assoc]
  ring

/-- The trace of the square of (A^2 B^2) is also that of ((AB)(AB)^*). -/
private theorem S_eq_mul_adjoint (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    S A B = realTrace (((A * B) * (A * B)ᴴ) ^ 2) := by
  simpa only [S, conjTranspose_mul, hA.eq, hB.eq, pow_succ, pow_zero, one_mul, mul_assoc] using
    realTrace_mul_comm A (A * (B * (B * (A * (A * (B * B))))))

private theorem realTrace_add_sq (X Y : Matrix n n ℂ) :
    realTrace ((X + Y) ^ 2) = realTrace (X ^ 2) + 2 * realTrace (X * Y) + realTrace (Y ^ 2) := by
  simp only [pow_two, add_mul, mul_add, realTrace_add, realTrace_mul_comm Y X]
  ring

private theorem realTrace_add_four (X Y : Matrix n n ℂ) :
    realTrace ((X + Y) ^ 4) =
      realTrace (X ^ 4) + realTrace (Y ^ 4) +
      4 * realTrace (X ^ 3 * Y) + 4 * realTrace (Y ^ 3 * X) +
      4 * realTrace (X ^ 2 * Y ^ 2) + 2 * realTrace ((X * Y) ^ 2) := by
  have hXXXY : realTrace (X ^ 2 * (Y * X)) = realTrace (X ^ 3 * Y) := by
    calc
      _ = realTrace ((X ^ 2 * Y) * X) := congrArg realTrace (mul_assoc _ _ _).symm
      _ = realTrace (X * (X ^ 2 * Y)) := realTrace_mul_comm _ _
      _ = _ := congrArg realTrace (by rw [pow_succ' X 2, mul_assoc])
  have hYYYX : realTrace (Y ^ 2 * (X * Y)) = realTrace (Y ^ 3 * X) := by
    calc
      _ = realTrace ((Y ^ 2 * X) * Y) := congrArg realTrace (mul_assoc _ _ _).symm
      _ = realTrace (Y * (Y ^ 2 * X)) := realTrace_mul_comm _ _
      _ = _ := congrArg realTrace (by rw [pow_succ' Y 2, mul_assoc])
  have hXYYX : realTrace ((X * Y) * (Y * X)) = realTrace (X ^ 2 * Y ^ 2) := by
    calc
      _ = realTrace ((X * (Y * Y)) * X) := congrArg realTrace (by simp only [mul_assoc])
      _ = realTrace (X * (X * (Y * Y))) := realTrace_mul_comm _ _
      _ = _ := congrArg realTrace (by rw [pow_two X, pow_two Y, mul_assoc])
  have hYXYX : realTrace ((Y * X) ^ 2) = realTrace ((X * Y) ^ 2) := by
    simpa only [pow_two, mul_assoc] using realTrace_mul_comm Y (X * (Y * X))
  rw [show (X + Y) ^ 4 = ((X ^ 2 + Y ^ 2) + (X * Y + Y * X)) ^ 2 by noncomm_ring]
  simp only [realTrace_add_sq, add_mul, mul_add, realTrace_add, hXXXY, hYYYX, hXYYX, hYXYX,
    ← pow_mul, show 2 * 2 = (4 : ℕ) by decide]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  ring

private theorem midpoint_four (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    8 * H A B = T A B + 4 * J A B + 2 * F A B + S A B := by
  let X := A * B
  have hscale (Y : Matrix n n ℂ) (r : ℝ) : realTrace (r • Y) = r * realTrace Y := by
    change (trace (r • Y)).re = r * (trace Y).re
    rw [trace_smul]
    exact RCLike.smul_re r (trace Y)
  have hT : realTrace (Xᴴ ^ 4) = realTrace (X ^ 4) := by
    rw [← conjTranspose_pow, realTrace_adjoint]
  have hJ₁ : realTrace (X ^ 3 * Xᴴ) = J A B := realTrace_mul_comm _ _
  have hJ₂ : realTrace (Xᴴ ^ 3 * X) = J A B := by
    rw [← realTrace_adjoint (Xᴴ ^ 3 * X), conjTranspose_mul,
      ← conjTranspose_pow, conjTranspose_conjTranspose]
    rfl
  have hF : realTrace (X ^ 2 * Xᴴ ^ 2) = F A B := by
    rw [realTrace_mul_comm, ← conjTranspose_pow]
    rfl
  have hS : realTrace ((X * Xᴴ) ^ 2) = S A B := (S_eq_mul_adjoint A B hA hB).symm
  change 8 * realTrace (((1 / 2 : ℝ) • (X + Xᴴ)) ^ 4) = _
  rw [smul_pow, hscale, realTrace_add_four, hT, hJ₁, hJ₂, hF, hS]
  change _ = realTrace (X ^ 4) + 4 * J A B + 2 * F A B + S A B
  ring

private theorem realTrace_Z_components (A B : Matrix n n ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    realTrace ((Z A B)ᴴ * Z A B) = U A B + 2 * C A B + F A B ∧
    realTrace ((Z A B) ^ 2) = S A B + 2 * J A B + T A B := by
  let D := A ^ 2 * B ^ 2
  let Y := (A * B) ^ 2
  have hD : Dᴴ = B ^ 2 * A ^ 2 := by
    simp only [D, conjTranspose_mul, conjTranspose_pow, hA.eq, hB.eq]
  have hY : Yᴴ = (B * A) ^ 2 := by
    simp only [Y, conjTranspose_pow, conjTranspose_mul, hA.eq, hB.eq]
  have hU : realTrace (Dᴴ * D) = U A B := by
    rw [hD]
    unfold D U
    calc
      _ = realTrace (B ^ 2 * (A ^ 4 * B ^ 2)) := congrArg realTrace (by noncomm_ring)
      _ = realTrace ((A ^ 4 * B ^ 2) * B ^ 2) := realTrace_mul_comm _ _
      _ = _ := congrArg realTrace (by noncomm_ring)
  have hC₁ : realTrace (Yᴴ * D) = C A B := by
    rw [hY]
    unfold D C
    calc
      _ = realTrace ((B * A * B) * (A ^ 3 * B ^ 2)) := congrArg realTrace (by noncomm_ring)
      _ = realTrace ((A ^ 3 * B ^ 2) * (B * A * B)) := realTrace_mul_comm _ _
      _ = _ := congrArg realTrace (by noncomm_ring)
  have hC₂ : realTrace (Dᴴ * Y) = C A B := by
    rw [← realTrace_adjoint (Dᴴ * Y), conjTranspose_mul, conjTranspose_conjTranspose, hC₁]
  have hJ : realTrace (D * Y) = J A B := by
    rw [← realTrace_adjoint (D * Y), conjTranspose_mul, hY, hD]
    unfold J
    rw [conjTranspose_mul, hA.eq, hB.eq]
    calc
      _ = realTrace ((B * A * B * A * B) * (B * A ^ 2)) := congrArg realTrace (by noncomm_ring)
      _ = realTrace ((B * A ^ 2) * (B * A * B * A * B)) := realTrace_mul_comm _ _
      _ = _ := congrArg realTrace (by noncomm_ring)
  constructor
  · change realTrace ((D + Y)ᴴ * (D + Y)) = _
    rw [conjTranspose_add]
    simp only [add_mul, mul_add, realTrace_add, hU, hC₁, hC₂]
    change U A B + C A B + (C A B + F A B) = _
    ring
  · change realTrace ((D + Y) ^ 2) = _
    rw [realTrace_add_sq, hJ]
    change S A B + 2 * J A B + realTrace (Y ^ 2) = _
    rw [← pow_mul]
    rfl

/-- The exact real trace gap, valid for any two finite Hermitian matrices. -/
private theorem trace_gap_decomposition (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (W A B - 70 * T A B) / 4 =
      2 * R A B + 2 * (P A B - S A B) + 2 * (Q A B - S A B) +
        4 * (S A B - F A B) + (S A B - T A B) + 16 * (H A B - T A B) := by
  obtain ⟨hNorm, hSquare⟩ := realTrace_Z_components A B hA hB
  rw [word_enumeration A B hA hB, R, hNorm, hSquare]
  linear_combination -2 * midpoint_four A B hA hB

#print axioms balancedWords44_perm
#print axioms word_enumeration
#print axioms S_eq_mul_adjoint
#print axioms trace_gap_decomposition

end RefinedBMV.Algebra44

open scoped ComplexOrder

namespace RefinedBMV

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real trace of a square is at most the squared Frobenius norm. -/
private theorem re_trace_sq_le_gram44 (Z : Matrix n n ℂ) :
    (trace (Z ^ 2)).re ≤ (trace (Zᴴ * Z)).re := by
  have h := Complex.le_def.mp (posSemidef_conjTranspose_mul_self (Z - Zᴴ)).trace_nonneg
  have hrev : (trace (Zᴴ * Zᴴ)).re = (trace (Z * Z)).re := by
    rw [← conjTranspose_mul, trace_conjTranspose]
    rfl
  simp only [Complex.zero_re, conjTranspose_sub, conjTranspose_conjTranspose, sub_mul, mul_sub,
    trace_sub, Complex.sub_re, trace_mul_comm Z Zᴴ, hrev] at h
  rw [pow_two]
  linarith [h.1]

/-- The two Gram matrices of a square matrix control the norm of its square. -/
private theorem square_gram_le_gram_square44 (M : Matrix n n ℂ) :
    (trace ((M ^ 2)ᴴ * M ^ 2)).re ≤ (trace ((M * Mᴴ) ^ 2)).re := by
  let L := M * Mᴴ
  let R := Mᴴ * M
  have hL : Lᴴ = L := (posSemidef_self_mul_conjTranspose M).isHermitian
  have hR : Rᴴ = R := (posSemidef_conjTranspose_mul_self M).isHermitian
  have h := (Complex.le_def.mp (posSemidef_conjTranspose_mul_self (L - R)).trace_nonneg).1
  have hLL : trace (R * R) = trace (L * L) := by
    calc
      _ = trace (Mᴴ * (M * Mᴴ * M)) := by simp only [R, mul_assoc]
      _ = trace ((M * Mᴴ * M) * Mᴴ) := trace_mul_comm _ _
      _ = _ := by simp only [L, mul_assoc]
  have hLR : trace (L * R) = trace ((M ^ 2)ᴴ * M ^ 2) := by
    dsimp [L, R]
    rw [conjTranspose_pow, pow_two, pow_two]
    simpa only [mul_assoc] using trace_mul_comm M (Mᴴ * Mᴴ * M)
  simp only [Complex.zero_re, conjTranspose_sub, hL, hR, sub_mul, mul_sub, trace_sub, Complex.sub_re,
    trace_mul_comm R L, hLL, hLR] at h
  change _ ≤ (trace (L ^ 2)).re
  rw [pow_two L]
  linarith

/-- The spread mixed word dominates the doubled block word by a weighted commutator square. -/
private theorem block_trace_le_spread44 (A B : Matrix n n ℂ) (hA : A.PosSemidef)
    (hB : B.IsHermitian) :
    (trace (A ^ 2 * B ^ 2 * A ^ 2 * B ^ 2)).re ≤
      (trace (A ^ 3 * B ^ 2 * A * B ^ 2)).re := by
  let K := A * B ^ 2 - B ^ 2 * A
  have hK : Kᴴ = -K := by
    simp only [K, conjTranspose_sub, conjTranspose_mul, conjTranspose_pow, hA.isHermitian.eq,
      hB.eq]
    abel
  have hn := RHLinalg.trace_mul_nonneg_of_posSemidef hA (hA.conjTranspose_mul_mul_same K)
  change 0 ≤ (trace (A * (Kᴴ * A * K))).re at hn
  have hexpand : A * (Kᴴ * A * K) =
      -(A ^ 2 * B ^ 2 * A ^ 2 * B ^ 2) + (A ^ 2 * B ^ 2 * A * B ^ 2) * A +
        A * (B ^ 2 * A ^ 3 * B ^ 2) - (A * B ^ 2 * A ^ 2 * B ^ 2) * A := by
    rw [hK]
    dsimp only [K]
    noncomm_ring
  have hp₁ : trace ((A ^ 2 * B ^ 2 * A * B ^ 2) * A) =
      trace (A ^ 3 * B ^ 2 * A * B ^ 2) := by
    rw [trace_mul_comm]
    congr 1
    noncomm_ring
  have hp₂ : trace (A * (B ^ 2 * A ^ 3 * B ^ 2)) =
      trace (A ^ 3 * B ^ 2 * A * B ^ 2) := by
    calc
      _ = trace ((A * B ^ 2) * (A ^ 3 * B ^ 2)) := by simp only [mul_assoc]
      _ = _ := by rw [trace_mul_comm, ← mul_assoc]
  have hs : trace ((A * B ^ 2 * A ^ 2 * B ^ 2) * A) =
      trace (A ^ 2 * B ^ 2 * A ^ 2 * B ^ 2) := by
    rw [trace_mul_comm]
    congr 1
    noncomm_ring
  simp only [hexpand, trace_sub, trace_add, trace_neg, hp₁, hp₂, hs,
    Complex.sub_re, Complex.add_re, Complex.neg_re] at hn
  linarith

end RefinedBMV

open Filter
open scoped MatrixOrder Topology

namespace RefinedBMV

open private triangularization trace_pow_triangular sq_diag_le_gram_diag from
  D5.S3.Quantum.Analysis.RefinedBMVTracePower

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

private theorem trace_four_le_symmetrized_of_triangular (M : Mat) (hM : M.IsUpperTriangular)
    (hreal : ∀ i, (M i i).im = 0) :
    (trace (M ^ 4)).re ≤ (trace (((1 / 2 : ℝ) • (M + Mᴴ)) ^ 4)).re := by
  let X : Mat := (1 / 2 : ℝ) • (M + Mᴴ)
  have hX : Xᴴ = X := by
    simp only [X, conjTranspose_smul, star_trivial, conjTranspose_add, conjTranspose_conjTranspose]
    rw [add_comm Mᴴ M]
  have hdiag (i : Fin n) : X i i = M i i := by
    apply Complex.ext
    · simp [X, Matrix.smul_apply, Complex.mul_re, hreal]
      ring
    · simp [X, Matrix.smul_apply, Complex.mul_im, hreal]
  have hX2 : (X ^ 2)ᴴ = X ^ 2 := by rw [conjTranspose_pow, hX]
  have htrace : trace (X ^ 4) = trace ((X ^ 2)ᴴ * X ^ 2) := by
    rw [hX2, ← pow_add]
  change _ ≤ (trace (X ^ 4)).re
  rw [trace_pow_triangular _ hM, htrace]
  simp only [Matrix.trace, diag_apply, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hd : ‖M i i‖ ^ 2 ≤ ((X ^ 2) i i).re := by
    simpa only [hdiag, hX, ← pow_two] using sq_diag_le_gram_diag X i
  calc
    (M i i ^ 4).re ≤ ‖M i i ^ 4‖ := Complex.re_le_norm _
    _ = (‖M i i‖ ^ 2) ^ 2 := by rw [norm_pow, ← pow_mul]
    _ ≤ (((X ^ 2) i i).re) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hd 2
    _ ≤ ‖(X ^ 2) i i‖ ^ 2 := by
      have hnonneg := (sq_nonneg ‖M i i‖).trans hd
      exact pow_le_pow_left₀ hnonneg (Complex.re_le_norm _) 2
    _ ≤ _ := sq_diag_le_gram_diag (X ^ 2) i

private theorem trace_four_le_symmetrized_of_posDef (A B : Mat) (hA : A.PosSemidef)
    (hB : B.PosDef) :
    (trace ((A * B) ^ 4)).re ≤ (trace (((1 / 2 : ℝ) • (A * B + (A * B)ᴴ)) ^ 4)).re := by
  let S := CFC.sqrt B
  have hS : Sᴴ = S := (CFC.sqrt_nonneg B).posSemidef.isHermitian
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self _ hB.posSemidef.nonneg
  have hSu : IsUnit S := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
    (by rw [pow_two, hSS]; exact hB.isUnit)
  have hdS := (Matrix.isUnit_iff_isUnit_det S).mp hSu
  let P := S * A * S
  have hP : P.IsHermitian := by
    simpa only [P, hS] using (hA.conjTranspose_mul_mul_same S).isHermitian
  let V := hP.eigenvectorUnitary
  let d : Fin n → ℂ := fun i ↦ (hP.eigenvalues i : ℂ)
  let W := S⁻¹ * (V : Mat)
  have hW : IsUnit W := (Matrix.isUnit_nonsing_inv_iff.mpr hSu).mul (Unitary.isUnit_coe (U := V))
  have hV : P * (V : Mat) = (V : Mat) * diagonal d := by
    conv_lhs =>
      rw [hP.spectral_theorem, Unitary.conjStarAlgAut_apply, mul_assoc,
        Unitary.coe_star_mul_self, mul_one]
    rfl
  have hMW : (A * B) * W = W * diagonal d := by
    calc
      _ = (A * S) * (V : Mat) := by
        dsimp only [W]
        rw [← hSS, mul_assoc _ _ (S⁻¹ * _), mul_assoc S S,
          ← mul_assoc S S⁻¹, Matrix.mul_nonsing_inv S hdS, one_mul, mul_assoc]
      _ = S⁻¹ * (P * (V : Mat)) := by
        dsimp only [P]
        rw [← mul_assoc S⁻¹, ← mul_assoc S⁻¹, ← mul_assoc S⁻¹,
          Matrix.nonsing_inv_mul S hdS, one_mul]
      _ = _ := by rw [hV, ← mul_assoc]
  obtain ⟨U, hU⟩ := triangularization (A * B) W d hW hMW
  let f := Unitary.conjStarAlgAut ℂ _ (star U)
  let N := f (A * B)
  have hchar : N.charpoly = P.charpoly := by
    calc
      _ = (A * B).charpoly := by
        dsimp only [N, f]
        rw [Unitary.conjStarAlgAut_star_apply]
        change (((U : Mat)ᴴ * (A * B)) * (U : Mat)).charpoly = _
        have hUU : (U : Mat) * (U : Mat)ᴴ = 1 := Unitary.coe_mul_star_self U
        rw [charpoly_mul_comm, ← mul_assoc, hUU, one_mul]
      _ = _ := by
        rw [← hSS, ← mul_assoc, charpoly_mul_comm (A * S) S]
        simp only [P, mul_assoc]
  have hn : N.IsUpperTriangular := hU
  have hre (i : Fin n) : (N i i).im = 0 := by
    have hm : N i i ∈ spectrum ℂ N := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot,
        charpoly_of_isUpperTriangular N hn, Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hchar,
      ← Matrix.mem_spectrum_iff_isRoot_charpoly, hP.spectrum_eq_image_range] at hm
    rcases hm with ⟨r, _, hr⟩
    rw [← hr]
    simp
  have h := trace_four_le_symmetrized_of_triangular N hU hre
  have hf : f ((1 / 2 : ℝ) • (A * B + (A * B)ᴴ)) = (1 / 2 : ℝ) • (N + Nᴴ) := by
    change f (((1 / 2 : ℝ) : ℂ) • (A * B + star (A * B))) =
      (((1 / 2 : ℝ) : ℂ)) • (f (A * B) + star (f (A * B)))
    rw [map_smul, map_add, map_star]
  rw [← hf] at h
  change (trace (f (A * B) ^ 4)).re ≤ _ at h
  have hftrace (Y : Mat) : trace (f Y) = trace Y := trace_conjugation (star U) Y
  rwa [← map_pow, ← map_pow, hftrace, hftrace] at h

/-- The Hermitian part of a product of two PSD matrices controls its fourth trace moment. -/
private theorem trace_four_le_symmetrized44 (A B : Mat) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (trace ((A * B) ^ 4)).re ≤ (trace (((1 / 2 : ℝ) • (A * B + (A * B)ᴴ)) ^ 4)).re := by
  let C (t : ℝ) : Mat := B + t • (1 : Mat)
  let f (t : ℝ) : ℝ := (trace ((A * C t) ^ 4)).re
  let g (t : ℝ) : ℝ := (trace (((1 / 2 : ℝ) • (A * C t + (A * C t)ᴴ)) ^ 4)).re
  have hf : Continuous f := by dsimp only [f, C]; fun_prop
  have hg : Continuous g := by dsimp only [g, C]; fun_prop
  have h := le_of_tendsto_of_tendsto ((hf.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ))))
    ((hg.tendsto 0).mono_left nhdsWithin_le_nhds) (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      have hshift : (t • (1 : Mat)).PosDef := by
        change (((t : ℂ)) • (1 : Mat)).PosDef
        exact PosDef.one.smul (by simp [Complex.lt_def, ht'])
      exact trace_four_le_symmetrized_of_posDef A (C t) hA (by
        rw [show C t = t • (1 : Mat) + B by simp [C, add_comm]]
        exact hshift.add_posSemidef hB))
  simpa [f, g, C] using h

end RefinedBMV

namespace RefinedBMV

open Algebra44

variable {n : ℕ}

set_option maxHeartbeats 800000 in
/-- The refined BMV product comparison at bidegree (4,4) holds in every finite
complex dimension, including for singular positive semidefinite factors. -/
theorem product_bound44 (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    70 * (trace ((A * B) ^ 4)).re ≤
      ((balancedWords 4 4).map fun w ↦ (trace (evalWord A B w)).re).sum := by
  have hp : S A B ≤ P A B := by
    simpa only [S, P, realTrace, pow_two (A ^ 2 * B ^ 2), mul_assoc] using
      block_trace_le_spread44 A B hA hB.isHermitian
  have hq : S A B ≤ Q A B := by
    have hs : trace (B ^ 2 * A ^ 2 * B ^ 2 * A ^ 2) =
        trace ((A ^ 2 * B ^ 2) ^ 2) := by
      calc
        _ = trace (B ^ 2 * (A ^ 2 * B ^ 2 * A ^ 2)) := by simp only [mul_assoc]
        _ = trace ((A ^ 2 * B ^ 2 * A ^ 2) * B ^ 2) := trace_mul_comm _ _
        _ = _ := by simp only [pow_two (A ^ 2 * B ^ 2), mul_assoc]
    have hq' : trace (B ^ 3 * A ^ 2 * B * A ^ 2) =
        trace (A ^ 2 * B ^ 3 * A ^ 2 * B) := by
      calc
        _ = trace (A ^ 2 * (B ^ 3 * A ^ 2 * B)) := trace_mul_comm _ _
        _ = _ := by rw [← mul_assoc (A ^ 2), ← mul_assoc (A ^ 2)]
    have h := block_trace_le_spread44 B A hB hA.isHermitian
    rw [hs, hq'] at h
    exact h
  have hf : F A B ≤ S A B := by
    rw [S_eq_mul_adjoint A B hA.isHermitian hB.isHermitian]
    exact square_gram_le_gram_square44 (A * B)
  have htf : T A B ≤ F A B := by
    have h := re_trace_sq_le_gram44 ((A * B) ^ 2)
    rw [← pow_mul] at h
    exact h
  have ht := htf.trans hf
  have hh : T A B ≤ H A B := trace_four_le_symmetrized44 A B hA hB
  have hr : 0 ≤ R A B := sub_nonneg.mpr (re_trace_sq_le_gram44 (Z A B))
  change 70 * T A B ≤ W A B
  linarith [trace_gap_decomposition A B hA.isHermitian hB.isHermitian]

#print axioms product_bound44

end RefinedBMV

open NormedSpace
open scoped CStarAlgebra Matrix.Norms.L2Operator

namespace RefinedBMV

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "CMat" => CStarMatrix (Fin n) (Fin n) ℂ

section NonemptyDimension

variable [NeZero n]

private noncomputable def dyadicTrace44 (H K : Mat) (j : ℕ) : ℝ :=
  (trace ((exp (((2 : ℝ) ^ j)⁻¹ • H) * exp (((2 : ℝ) ^ j)⁻¹ • K)) ^
    (4 * 2 ^ j))).re

private theorem dyadicTrace44_step (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (j : ℕ) : dyadicTrace44 H K (j + 1) ≤ dyadicTrace44 H K j := by
  let s : ℝ := ((2 : ℝ) ^ (j + 1))⁻¹
  have hs : (2 : ℕ) • (s • H) = ((2 : ℝ) ^ j)⁻¹ • H := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    dsimp only [s]
    rw [pow_succ, _root_.mul_inv_rev]
    norm_num [← mul_assoc]
  have hs' : (2 : ℕ) • (s • K) = ((2 : ℝ) ^ j)⁻¹ • K := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    dsimp only [s]
    rw [pow_succ, _root_.mul_inv_rev]
    norm_num [← mul_assoc]
  have h := trace_mul_two_pow_le (exp (s • H)) (exp (s • K))
    (exp_posDef (hermitian_real_smul hH s)) (exp_posDef (hermitian_real_smul hK s))
    (4 * 2 ^ j)
  rw [← Matrix.exp_nsmul, ← Matrix.exp_nsmul, hs, hs'] at h
  have hp : 2 * (4 * 2 ^ j) = 4 * 2 ^ (j + 1) := by rw [pow_succ]; ring
  rw [hp] at h
  exact h

private theorem dyadicTrace44_tendsto (H K : Mat) :
    Tendsto (dyadicTrace44 H K) atTop (𝓝 (trace (exp ((4 : ℝ) • H + (4 : ℝ) • K))).re) := by
  letI : NormedAlgebra ℚ CMat := NormedAlgebra.restrictScalars ℚ ℂ _
  let f := CStarMatrix.ofMatrixStarAlgEquiv (n := Fin n) (A := ℂ)
  let g := f.symm
  have hc : Continuous (fun A : CMat ↦ (trace (g A)).re) :=
    Complex.continuous_re.comp (CStarMatrix.ofMatrixL.symm.continuous.matrix_trace)
  have ht : Tendsto (fun j : ℕ ↦ 4 * 2 ^ j) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℕ) < 2 by decide)).const_mul_atTop'
      (show (0 : ℕ) < 4 by decide)
  have h := (NormedSpace.trotter_product ((4 : ℝ) • f H) ((4 : ℝ) • f K)).comp ht
  have h' := hc.continuousAt.tendsto.comp h
  have hExp (X : CMat) : g (exp X) = exp (g X) :=
    NormedSpace.map_exp g CStarMatrix.ofMatrixL.symm.continuous X
  have hgs (r : ℝ) (A : CMat) : g (r • A) = r • g A := rfl
  have hScalar (j : ℕ) : ((↑(4 * 2 ^ j : ℕ) : ℝ)⁻¹ * 4) = ((2 : ℝ) ^ j)⁻¹ := by
    push_cast
    rw [_root_.mul_inv_rev, mul_assoc]
    norm_num
  let step (j : ℕ) (M : Mat) : CMat := ((↑(4 * 2 ^ j : ℕ) : ℝ)⁻¹) • ((4 : ℝ) • f M)
  have hstep (j : ℕ) (M : Mat) : g (step j M) = ((2 : ℝ) ^ j)⁻¹ • M := by
    change ((↑(4 * 2 ^ j : ℕ) : ℝ)⁻¹) • ((4 : ℝ) • M) = _
    rw [smul_smul, hScalar]
  have hseq : (fun j : ℕ ↦ (trace (g ((exp (step j H) * exp (step j K)) ^
      (4 * 2 ^ j)))).re) = dyadicTrace44 H K := by
    funext j
    rw [map_pow g, map_mul g, hExp, hExp, hstep j H, hstep j K]
    rfl
  rw [← hseq]
  change Tendsto (fun j : ℕ ↦ (trace (g ((exp (step j H) * exp (step j K)) ^
      (4 * 2 ^ j)))).re) atTop (𝓝 (trace (g (exp ((4 : ℝ) • f H + (4 : ℝ) • f K)))).re) at h'
  simpa only [hExp, map_add, hgs, g, StarAlgEquiv.symm_apply_apply] using h'

/-- Dyadic trace-power comparison against the Trotter limit. -/
private theorem trace_exp_sum_le_fourth (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (trace (exp ((4 : ℝ) • H + (4 : ℝ) • K))).re ≤
      (trace ((exp H * exp K) ^ 4)).re := by
  have hmono : Antitone (dyadicTrace44 H K) :=
    antitone_nat_of_succ_le (dyadicTrace44_step H K hH hK)
  have h := le_of_tendsto' (dyadicTrace44_tendsto H K) (fun j ↦ hmono (Nat.zero_le j))
  simpa [dyadicTrace44] using h

end NonemptyDimension

/-- The sum of the seventy real word traces of the exponentials dominates
seventy times the trace of the exponential of four times the sum. -/
theorem exponential_bound44 (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    70 * (trace (exp ((4 : ℝ) • H + (4 : ℝ) • K))).re ≤
      ((balancedWords 4 4).map fun w ↦ (trace (evalWord (exp H) (exp K) w)).re).sum := by
  by_cases hn : n = 0
  · subst n
    simp [trace_eq_zero_of_isEmpty]
  letI : NeZero n := ⟨hn⟩
  have he := trace_exp_sum_le_fourth H K hH hK
  exact (mul_le_mul_of_nonneg_left he (by norm_num)).trans
    (product_bound44 _ _ (exp_posDef hH).posSemidef (exp_posDef hK).posSemidef)

#print axioms exponential_bound44

end RefinedBMV
