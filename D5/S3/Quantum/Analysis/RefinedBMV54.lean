/- GID: D5/S3/Quantum/Analysis/RefinedBMV54
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV54
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hägele's refined BMV lower bounds with five copies of the first factor. -/

import D5.S3.Quantum.Analysis.RefinedBMV44
import Mathlib.Data.List.Lex

/-! # The refined BMV product and exponential comparisons at bidegree (5,4) -/

open Matrix NormedSpace Filter
open scoped ComplexOrder MatrixOrder Topology Matrix.Norms.L2Operator

noncomputable section

namespace RefinedBMV.Algebra54

open private evalWord_append43 from D5.S3.Quantum.Analysis.RefinedBMV43
open private evalWord_reverse from D5.S3.Quantum.Analysis.RefinedBMV44

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "𝔞" => true
local notation "𝔟" => false

private def w₀ : List Bool := [𝔞, 𝔞, 𝔟, 𝔟]
private def w₁ : List Bool := [𝔞, 𝔟, 𝔞, 𝔟]
private def w₂ : List Bool := [𝔞, 𝔟, 𝔟, 𝔞]
private def w₃ : List Bool := [𝔟, 𝔞, 𝔞, 𝔟]
private def w₄ : List Bool := [𝔟, 𝔞, 𝔟, 𝔞]
private def w₅ : List Bool := [𝔟, 𝔟, 𝔞, 𝔞]

-- Positive and negative summands of each certificate vector, with multiplicity.
private def pos₁ : List (List Bool) := [w₀, w₁, w₃]
private def neg₁ : List (List Bool) := [w₂, w₄, w₅]
private def pos₂ : List (List Bool) := [w₂, w₂, w₃, w₃]
private def neg₂ : List (List Bool) := [w₄, w₄, w₄, w₅]
private def pos₃ : List (List Bool) := [w₃]
private def neg₃ : List (List Bool) := [w₄]
private def pos₄ : List (List Bool) := [w₄]
private def neg₄ : List (List Bool) := [w₅]

private def evalSum (A B : Matrix n n ℂ) (words : List (List Bool)) : Matrix n n ℂ :=
  (words.map (evalWord A B)).sum

def u₁ (A B : Matrix n n ℂ) : Matrix n n ℂ := evalSum A B pos₁ - evalSum A B neg₁
def u₂ (A B : Matrix n n ℂ) : Matrix n n ℂ := evalSum A B pos₂ - evalSum A B neg₂
def u₃ (A B : Matrix n n ℂ) : Matrix n n ℂ := evalSum A B pos₃ - evalSum A B neg₃
def u₄ (A B : Matrix n n ℂ) : Matrix n n ℂ := evalSum A B pos₄ - evalSum A B neg₄

private def realWordTrace (A B : Matrix n n ℂ) (w : List Bool) : ℝ :=
  (trace (evalWord A B w)).re

private def traceSum (A B : Matrix n n ℂ) (words : List (List Bool)) : ℝ :=
  (words.map (realWordTrace A B)).sum

private theorem real_trace_evalSum (A B : Matrix n n ℂ) (words : List (List Bool)) :
    (trace (evalSum A B words)).re = traceSum A B words := by
  rw [evalSum, trace_list_sum]
  change _ = (words.map fun w ↦ (trace (evalWord A B w)).re).sum
  simpa only [List.map_map, Function.comp_def, Complex.reCLM_apply]
    using (map_list_sum Complex.reCLM ((words.map (evalWord A B)).map trace))

private def gramWords (p q : List (List Bool)) : List (List Bool) :=
  p.flatMap fun w ↦ q.map fun v ↦ w.reverse ++ 𝔞 :: v

private theorem evalSum_gramWords (A B : Matrix n n ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (p q : List (List Bool)) :
    evalSum A B (gramWords p q) = (evalSum A B p)ᴴ * A * evalSum A B q := by
  simp only [gramWords, evalSum, List.flatMap_def, List.map_flatten,
    List.sum_flatten, List.map_map, Function.comp_def, evalWord_append43, evalWord_reverse A B hA hB,
    evalWord, List.sum_map_mul_left, List.sum_map_mul_right, conjTranspose_list_sum, mul_assoc]

private def squarePos (p q : List (List Bool)) : List (List Bool) :=
  gramWords p p ++ gramWords q q

private def squareNeg (p q : List (List Bool)) : List (List Bool) :=
  gramWords p q ++ gramWords q p

private theorem traceSum_append (A B : Matrix n n ℂ) (p q : List (List Bool)) :
    traceSum A B (p ++ q) = traceSum A B p + traceSum A B q := by
  simp only [traceSum, List.map_append, List.sum_append]

private theorem square_trace (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (p q : List (List Bool)) :
    let U := evalSum A B p - evalSum A B q
    (trace (Uᴴ * A * U)).re = traceSum A B (squarePos p q) - traceSum A B (squareNeg p q) := by
  simp only [squarePos, squareNeg, traceSum_append]
  simp only [← real_trace_evalSum, evalSum_gramWords A B hA hB, conjTranspose_sub,
    sub_mul, mul_sub, trace_sub, Complex.sub_re]
  ring

private def repeatWords (k : ℕ) (words : List (List Bool)) : List (List Bool) :=
  (List.replicate k words).flatten

private theorem traceSum_repeat (A B : Matrix n n ℂ) (k : ℕ) (words : List (List Bool)) :
    traceSum A B (repeatWords k words) = (k : ℝ) * traceSum A B words := by
  simp only [traceSum, repeatWords, List.map_flatten, List.sum_flatten, List.map_replicate,
    List.sum_replicate, nsmul_eq_mul]

private def gramPos : List (List Bool) :=
  squarePos pos₁ neg₁ ++ squarePos pos₂ neg₂ ++
    repeatWords 8 (squarePos pos₃ neg₃) ++ squarePos pos₄ neg₄

private def gramNeg : List (List Bool) :=
  squareNeg pos₁ neg₁ ++ squareNeg pos₂ neg₂ ++
    repeatWords 8 (squareNeg pos₃ neg₃) ++ squareNeg pos₄ neg₄

private def alternatingWord : List Bool := [𝔞, 𝔞, 𝔟, 𝔞, 𝔟, 𝔞, 𝔟, 𝔞, 𝔟]

private def rotations (w : List Bool) : List (List Bool) :=
  (List.range w.length).map w.rotate

private def representative (w : List Bool) : List Bool :=
  ((rotations w ++ rotations w.reverse).min?).getD w

private theorem realWordTrace_representative (A B : Matrix n n ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (w : List Bool) :
    realWordTrace A B (representative w) = realWordTrace A B w := by
  unfold representative
  cases h : (rotations w ++ rotations w.reverse).min? with
  | none => rfl
  | some r =>
    simp only [Option.getD_some]
    rcases List.mem_append.mp (List.min?_mem h) with hr | hr
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr
      exact congrArg Complex.re (evalWord_rotate_trace43 A B w k)
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr
      simp only [realWordTrace, evalWord_rotate_trace43, evalWord_reverse A B hA hB,
        trace_conjTranspose, Complex.star_def, Complex.conj_re]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem coefficient_perm :
    ((balancedWords 5 4 ++ repeatWords 9 gramNeg).map representative).Perm
      ((List.replicate 126 alternatingWord ++ repeatWords 9 gramPos).map representative) := by
  simp only [balancedWords, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide +kernel

/-- The exact weighted four-square identity for the real trace gap. The
denominator nine converts the ordered word sum into a sum over cyclic orbits. -/
private theorem trace_gap_decomposition (A B : Matrix n n ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    (((balancedWords 5 4).map fun w ↦ (trace (evalWord A B w)).re).sum -
      126 * (trace (A * (A * B) ^ 4)).re) / 9 =
        (trace ((u₁ A B)ᴴ * A * u₁ A B)).re + (trace ((u₂ A B)ᴴ * A * u₂ A B)).re +
          8 * (trace ((u₃ A B)ᴴ * A * u₃ A B)).re + (trace ((u₄ A B)ᴴ * A * u₄ A B)).re := by
  have h := (coefficient_perm.map (realWordTrace A B)).sum_eq
  simp only [List.map_map, Function.comp_def, realWordTrace_representative A B hA hB] at h
  change traceSum A B (_ ++ _) = traceSum A B (_ ++ _) at h
  have hAlt : realWordTrace A B alternatingWord = (trace (A * (A * B) ^ 4)).re := by
    simp only [realWordTrace, alternatingWord, evalWord, pow_succ, pow_zero,
      one_mul, mul_one, mul_assoc]
  simp only [traceSum_append, traceSum_repeat, gramNeg, gramPos, Nat.cast_ofNat] at h
  have hRep : traceSum A B (List.replicate 126 alternatingWord) =
      126 * (trace (A * (A * B) ^ 4)).re := by
    simp only [traceSum, List.map_replicate, List.sum_replicate, nsmul_eq_mul, Nat.cast_ofNat, hAlt]
  rw [hRep] at h
  change (traceSum A B _ - _) / 9 = _
  simp only [u₁, u₂, u₃, u₄, square_trace A B hA hB]
  linarith only [h]

/-- For PSD `A` and Hermitian `B`, the average word trace dominates the
real trace of the alternating product with one extra `A`. -/
private theorem trace_alternating_le_wordSum (A B : Matrix n n ℂ) (hA : A.PosSemidef)
    (hB : B.IsHermitian) :
    126 * (trace (A * (A * B) ^ 4)).re ≤
      ((balancedWords 5 4).map fun w ↦ (trace (evalWord A B w)).re).sum := by
  have hNonneg (U : Matrix n n ℂ) : 0 ≤ (trace (Uᴴ * A * U)).re :=
    (Complex.le_def.mp (hA.conjTranspose_mul_mul_same U).trace_nonneg).1
  have hGap := trace_gap_decomposition A B hA.isHermitian hB
  linarith only [hGap, hNonneg (u₁ A B), hNonneg (u₂ A B), hNonneg (u₃ A B), hNonneg (u₄ A B)]

end RefinedBMV.Algebra54

namespace RefinedBMV

open private trace_cycle_power from D5.S3.Quantum.Analysis.RefinedBMVTracePower
open private trace_exp_sum_le_fourth re_trace_sq_le_gram44 square_gram_le_gram_square44
  Algebra44.S_eq_mul_adjoint from D5.S3.Quantum.Analysis.RefinedBMV44

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

private theorem trace_four_le_four_blocks (X Y : Mat)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (trace ((X * Y) ^ 4)).re ≤ (trace (X ^ 4 * Y ^ 4)).re := by
  let D := X ^ 2 * Y ^ 2
  have hd : trace (Dᴴ * D) = trace (X ^ 4 * Y ^ 4) := by
    calc
      _ = trace (Y ^ 2 * (X ^ 4 * Y ^ 2)) := by
        apply congrArg trace
        simp only [D, conjTranspose_mul, conjTranspose_pow, hX.eq, hY.eq]
        noncomm_ring
      _ = trace ((X ^ 4 * Y ^ 2) * Y ^ 2) := trace_mul_comm _ _
      _ = _ := by apply congrArg trace; noncomm_ring
  have hFT := re_trace_sq_le_gram44 ((X * Y) ^ 2)
  rw [← pow_mul] at hFT
  have hSF := square_gram_le_gram_square44 (X * Y)
  have hs := Algebra44.S_eq_mul_adjoint X Y hX hY
  change (trace (D ^ 2)).re = (trace (((X * Y) * (X * Y)ᴴ) ^ 2)).re at hs
  have hSU := re_trace_sq_le_gram44 D
  rw [hd] at hSU
  exact hFT.trans (hSF.trans (hs.ge.trans hSU))

set_option maxHeartbeats 800000 in
private theorem four_copy_bound_of_root (X B : Mat) (hX : X.PosSemidef)
    (hB : B.IsHermitian) :
    126 * (trace ((X ^ 5 * B) ^ 4)).re ≤
      ((balancedWords 5 4).map fun w ↦ (trace (evalWord (X ^ 4) B w)).re).sum := by
  let Y := X ^ 2 * B * X ^ 2
  have hX2 : (X ^ 2)ᴴ = X ^ 2 := by rw [conjTranspose_pow, hX.isHermitian.eq]
  have hY : Y.IsHermitian := by
    change Yᴴ = Y
    simp only [Y, conjTranspose_mul, hX2, hB.eq, mul_assoc]
  have h₁ : trace ((X ^ 5 * B) ^ 4) = trace ((X * Y) ^ 4) := by
    calc
      _ = trace ((X ^ 2 * (X ^ 3 * B)) ^ 4) := by
        apply congrArg trace
        noncomm_ring
      _ = trace (((X ^ 3 * B) * X ^ 2) ^ 4) := trace_cycle_power _ _ 4
      _ = _ := by
        dsimp only [Y]
        apply congrArg trace
        noncomm_ring
  have h₂ : trace (X ^ 4 * Y ^ 4) = trace (X ^ 4 * (X ^ 4 * B) ^ 4) := by
    calc
      _ = trace ((X ^ 6 * B * (X ^ 4 * B) ^ 3) * X ^ 2) := by
        dsimp only [Y]
        apply congrArg trace
        noncomm_ring
      _ = trace (X ^ 2 * (X ^ 6 * B * (X ^ 4 * B) ^ 3)) := trace_mul_comm _ _
      _ = _ := by
        apply congrArg trace
        noncomm_ring
  have hp := trace_four_le_four_blocks X Y hX.isHermitian hY
  rw [← h₁, h₂] at hp
  exact (mul_le_mul_of_nonneg_left hp (by norm_num)).trans
    (Algebra54.trace_alternating_le_wordSum (X ^ 4) B (hX.pow 4) hB)

/-- The product bound for five copies of A and four copies of B. -/
theorem product_bound54 (A B : Mat) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    126 * (trace (((A ^ (5 / 4 : ℝ)) * B) ^ 4)).re ≤
      ((balancedWords 5 4).map fun w ↦ (trace (evalWord A B w)).re).sum := by
  let X := A ^ (1 / 4 : ℝ)
  have hX : 0 ≤ X := CFC.rpow_nonneg
  have hpow (k : ℕ) : X ^ k = A ^ ((1 / 4 : ℝ) * k) := by
    rw [← CFC.rpow_natCast X k hX]
    exact CFC.rpow_rpow_of_exponent_nonneg A (1 / 4) k (by norm_num) (by positivity) hA.nonneg
  have h4 : X ^ (4 : ℕ) = A := by
    rw [hpow, show (1 / 4 : ℝ) * (↑(4 : ℕ) : ℝ) = 1 by norm_num, CFC.rpow_one A hA.nonneg]
  have h5 : X ^ (5 : ℕ) = A ^ (5 / 4 : ℝ) := by
    rw [hpow]
    congr 1
    norm_num
  simpa only [h4, h5] using four_copy_bound_of_root X B (Matrix.nonneg_iff_posSemidef.mp hX) hB

/-- The exponential bound for five copies of exp H and four copies of exp K. -/
theorem exponential_bound54 (H K : Mat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    126 * (trace (exp ((5 : ℝ) • H + (4 : ℝ) • K))).re ≤
      ((balancedWords 5 4).map fun w ↦ (trace (evalWord (exp H) (exp K) w)).re).sum := by
  by_cases hn : n = 0
  · subst n
    simp [trace_eq_zero_of_isEmpty]
  letI : NeZero n := ⟨hn⟩
  let T : Mat := (1 / 4 : ℝ) • H
  have hT : T.IsHermitian := hermitian_real_smul hH _
  have hpow (k : ℕ) : (exp T) ^ k = exp ((k : ℝ) • T) := by
    rw [Nat.cast_smul_eq_nsmul, Matrix.exp_nsmul]
  have h4 : (exp T) ^ (4 : ℕ) = exp H := by
    rw [hpow]
    norm_num [T, smul_smul]
  have h5 : (exp T) ^ (5 : ℕ) = exp ((5 : ℝ) • T) := by
    simpa only [Nat.cast_ofNat] using hpow 5
  have hscale : (4 : ℝ) • ((5 : ℝ) • T) = (5 : ℝ) • H := by
    dsimp only [T]
    rw [smul_smul, smul_smul]
    norm_num
  have hb := four_copy_bound_of_root (exp T) (exp K) (exp_posDef hT).posSemidef
    hK.exp
  rw [h4, h5] at hb
  have ht := trace_exp_sum_le_fourth ((5 : ℝ) • T) K (hermitian_real_smul hT _) hK
  rw [hscale] at ht
  exact (mul_le_mul_of_nonneg_left ht (by norm_num)).trans hb

#print axioms product_bound54
#print axioms exponential_bound54

end RefinedBMV
