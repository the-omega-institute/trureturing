/- GID: D5/S3/Quantum/Analysis/RefinedBMV43
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV43
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite-dimensional refined BMV product and exponential bounds at bidegree (4,3). -/

import D5.S3.Quantum.Analysis.RefinedBMV43Kernel
import D5.S3.Quantum.Analysis.RefinedBMVLowerBound
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.List.Rotate

/-! # The refined BMV (4,3) product and exponential bounds -/

open private walk walk_rotate trace_pow_walk
  from D5.S3.Quantum.Analysis.RefinedBMV33
open private exp_posDef hermitian_real_smul
  from D5.S3.Quantum.Analysis.RefinedBMVLowerBound

open Matrix NormedSpace
open scoped ComplexOrder BigOperators

noncomputable section

namespace RefinedBMV

variable {n : Type*} [Fintype n] [DecidableEq n]

private def gapWord43 (g : ℕ × ℕ × ℕ) : List Bool :=
  List.replicate g.1 true ++ [false] ++ List.replicate g.2.1 true ++ [false] ++
    List.replicate g.2.2 true ++ [false]

private def rotations43 (w : List Bool) : List (List Bool) :=
  (List.range 7).map w.rotate

private def traceGaps43 (A B : Matrix n n ℂ) (g : ℕ × ℕ × ℕ) : ℂ :=
  trace (A ^ g.1 * (B * (A ^ g.2.1 * (B * (A ^ g.2.2 * B)))))

/-- The mean trace of the words with four copies of A and three copies of B. -/
def mean43 (A B : Matrix n n ℂ) : ℂ :=
  (gapOrbits43.map (traceGaps43 A B)).sum / 5

/-- The recursive word enumeration contains exactly thirty-five distinct words. -/
theorem balancedWords43_count :
    (balancedWords 4 3).length = 35 ∧ (balancedWords 4 3).Nodup := by
  simp only [balancedWords, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  decide

private theorem evalWord_append43 (A B : Matrix n n ℂ) (u v : List Bool) :
    evalWord A B (u ++ v) = evalWord A B u * evalWord A B v := by
  induction u with
  | nil => simp [evalWord]
  | cons a u ih => cases a <;> simp [evalWord, ih, mul_assoc]

private theorem evalWord_rotate_trace43 (A B : Matrix n n ℂ) (w : List Bool) (k : ℕ) :
    trace (evalWord A B (w.rotate k)) = trace (evalWord A B w) := by
  rw [List.rotate_eq_drop_append_take_mod, evalWord_append43, trace_mul_comm,
    ← evalWord_append43, List.take_append_drop]

private theorem evalWord_block43 (A B : Matrix n n ℂ) (p : ℕ) (w : List Bool) :
    evalWord A B (List.replicate p true ++ w) = A ^ p * evalWord A B w := by
  induction p with
  | zero => simp
  | succ p ih =>
    simp [List.replicate_succ, evalWord, ih, pow_succ', mul_assoc]

private theorem evalWord_gap_trace43 (A B : Matrix n n ℂ) (g : ℕ × ℕ × ℕ) :
    trace (evalWord A B (gapWord43 g)) = traceGaps43 A B g := by
  simp [gapWord43, traceGaps43, List.append_assoc, evalWord_block43, evalWord]

private theorem rotations_trace43 (A B : Matrix n n ℂ) (g : ℕ × ℕ × ℕ) :
    ((rotations43 (gapWord43 g)).map (fun w ↦ trace (evalWord A B w))).sum =
      7 * traceGaps43 A B g := by
  simp [rotations43, List.map_map, Function.comp_def, evalWord_rotate_trace43,
    evalWord_gap_trace43]
  ring

/-- The five cyclic orbits account exactly for the recursively enumerated word mean. -/
theorem mean43_eq_enumerated (A B : Matrix n n ℂ) :
    mean43 A B = ((balancedWords 4 3).map (fun w ↦ trace (evalWord A B w))).sum / 35 := by
  have h : (balancedWords 4 3).Perm (gapOrbits43.flatMap (rotations43 ∘ gapWord43)) := by
    simp only [balancedWords, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    decide
  rw [(h.map (fun w ↦ trace (evalWord A B w))).sum_eq]
  simp only [mean43, gapOrbits43, List.flatMap_cons, List.flatMap_nil, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Function.comp_apply, rotations_trace43]
  ring

private theorem traceGaps43_rotate (A B : Matrix n n ℂ) (p q r : ℕ) :
    traceGaps43 A B (q, r, p) = traceGaps43 A B (p, q, r) := by
  simpa only [traceGaps43, mul_assoc] using
    trace_mul_comm (A ^ q * (B * (A ^ r * B))) (A ^ p * B)

private theorem sum_traceGaps43 (A B : Matrix n n ℂ) :
    (gaps43.map (traceGaps43 A B)).sum = 15 * mean43 A B := by
  have h (p q r : ℕ) :
      ([(p, q, r), (q, r, p), (r, p, q)].map (traceGaps43 A B)).sum =
        3 * traceGaps43 A B (p, q, r) := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [traceGaps43_rotate A B q r p, traceGaps43_rotate A B p q r]
    ring
  have hsum (l : List (ℕ × ℕ × ℕ)) :
      ((l.flatMap fun (p, q, r) ↦ [(p, q, r), (q, r, p), (r, p, q)]).map
        (traceGaps43 A B)).sum = 3 * (l.map (traceGaps43 A B)).sum := by
    induction l with
    | nil => simp
    | cons g l ih =>
      obtain ⟨p, q, r⟩ := g
      rw [List.flatMap_cons, List.map_append, List.sum_append, h, ih]
      simp only [List.map_cons, List.sum_cons]
      ring
  rw [gaps43, hsum, mean43]
  ring

private theorem mean43_map {m : Type*} [Fintype m] [DecidableEq m]
    (f : Matrix n n ℂ ≃ₐ[ℂ] Matrix m m ℂ)
    (hf : ∀ M, trace (f M) = trace M) (A B : Matrix n n ℂ) :
    mean43 (f A) (f B) = mean43 A B := by
  have h : traceGaps43 (f A) (f B) = traceGaps43 A B := by
    funext g
    simp only [traceGaps43, ← map_pow f, ← map_mul f, hf]
  simp only [mean43, h]

omit [DecidableEq n] in
private theorem sum_walk43 {α : Type*} (B : Matrix n n ℂ) (l : List α)
    (f : α → n → n → n → ℂ) :
    (l.map (fun a ↦ walk B (f a))).sum =
      walk B (fun i j k ↦ (l.map (fun a ↦ f a i j k)).sum) := by
  induction l with
  | nil => exact (map_zero (walk B)).symm
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, ← map_add]
    rfl

private theorem trace_gap43 (a : n → ℝ) (B : Matrix n n ℂ) :
    15 * (mean43 ((diagonal fun i ↦ (a i : ℂ)) ^ 3) B -
      trace (((diagonal fun i ↦ (a i : ℂ)) ^ 4 * B) ^ 3)) =
      walk B (fun i j k ↦ (defect43 (a i) (a j) (a k) : ℂ)) := by
  let d : n → ℂ := fun i ↦ a i
  let f (g : ℕ × ℕ × ℕ) (i j k : n) : ℂ :=
    (d i ^ 3) ^ g.1 * (d j ^ 3) ^ g.2.1 * (d k ^ 3) ^ g.2.2
  have htrace : traceGaps43 ((diagonal d) ^ 3) B = fun g ↦ walk B (f g) := by
    funext g
    simpa only [traceGaps43, f, pow_mul, mul_assoc] using
      trace_pow_walk B d (3 * g.1) (3 * g.2.1) (3 * g.2.2)
  have hc : trace (((diagonal d) ^ 4 * B) ^ 3) =
      walk B (fun i j k ↦ d i ^ 4 * d j ^ 4 * d k ^ 4) := by
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using trace_pow_walk B d 4 4 4
  change 15 * (mean43 ((diagonal d) ^ 3) B - trace (((diagonal d) ^ 4 * B) ^ 3)) = _
  rw [mul_sub, ← sum_traceGaps43, hc, htrace, sum_walk43 B gaps43 f]
  change walk B _ - (15 : ℂ) • walk B _ = _
  rw [← map_smul, ← map_sub]
  congr 1
  funext i j k
  simp only [defect43, f, d, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, gaps43,
    gapOrbits43, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

private def centeredWeight43 (a : n → ℝ) (i j k : n) : ℂ :=
  ((a i - a j) * (a i - a k) * centeredKernel43 (a i) (a j) (a k) : ℝ)

omit [DecidableEq n] in
private theorem walk_defect43 (a : n → ℝ) (ha : ∀ i, 0 ≤ a i) (B : Matrix n n ℂ) :
    walk B (fun i j k ↦ (defect43 (a i) (a j) (a k) : ℂ)) =
      3 * walk B (centeredWeight43 a) := by
  classical
  have h : (fun i j k ↦ (defect43 (a i) (a j) (a k) : ℂ)) =
      centeredWeight43 a + (fun i j k ↦ centeredWeight43 a j k i) +
        (fun i j k ↦ centeredWeight43 a k i j) := by
    funext i j k
    simp only [Pi.add_apply, centeredWeight43]
    exact_mod_cast defect43_eq_cyclic (a i) (a j) (a k) (ha i) (ha j) (ha k)
  rw [h, map_add, map_add, walk_rotate B (fun i j k ↦ centeredWeight43 a j k i),
    walk_rotate B (centeredWeight43 a)]
  ring

omit [DecidableEq n] in
private theorem centered_form43 (a : n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (B : Matrix n n ℂ) (hB : B.PosSemidef) (i : n) :
    0 ≤ ∑ j, ∑ k, B i j * B j k * B k i * centeredWeight43 a i j k := by
  classical
  let G : Matrix n n ℝ := Matrix.of fun j k ↦ centeredKernel43 (a i) (a j) (a k)
  have hG : G.PosSemidef := centeredKernel43_psd (a i) (ha i) a ha
  have hc := D5.S3.Weil.Probability.FiniteGaussianSchoenberg.ofReal_posSemidef G hG
  let v : n → ℂ := fun j ↦ ((a i - a j : ℝ) : ℂ) * B j i
  have hp : (B ⊙ G.map Complex.ofReal).PosSemidef := hB.hadamard hc
  convert hp.dotProduct_mulVec_nonneg v using 1
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  have hstar : star (B j i) = B i j := congrFun (congrFun hB.isHermitian i) j
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  simp only [centeredWeight43, Pi.star_apply, v, star_mul, hreal, hstar, hadamard_apply,
    Matrix.map_apply, G, Matrix.of_apply, Complex.ofReal_mul]
  ring

private theorem E43_diagonal (a : n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (B : Matrix n n ℂ) (hB : B.PosSemidef) :
    trace (((diagonal fun i ↦ (a i : ℂ)) ^ 4 * B) ^ 3) ≤
      mean43 ((diagonal fun i ↦ (a i : ℂ)) ^ 3) B := by
  have h := trace_gap43 a B
  rw [walk_defect43 a ha B] at h
  have hn : 0 ≤ walk B (centeredWeight43 a) :=
    Finset.sum_nonneg fun i _ ↦ centered_form43 a ha B hB i
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hn
  have hRe := congrArg Complex.re h
  have hIm := congrArg Complex.im h
  norm_num [Complex.mul_re, Complex.sub_re] at hRe
  norm_num [Complex.mul_im, Complex.sub_im] at hIm
  exact Complex.le_def.mpr ⟨by linarith, by linarith⟩

/-- The refined BMV product bound in cube-root form for arbitrary PSD matrices. -/
theorem E43_cubeRoot (X B : Matrix n n ℂ) (hX : X.PosSemidef) (hB : B.PosSemidef) :
    trace ((X ^ 4 * B) ^ 3) ≤ mean43 (X ^ 3) B := by
  rcases isEmpty_or_nonempty n with hempty | _
  · let _ := hempty
    simp [mean43, gapOrbits43, traceGaps43, trace_eq_zero_of_isEmpty]
  let U := hX.isHermitian.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ _ (star U)
  have hB' : (f B).PosSemidef := by
    change (Unitary.conjStarAlgAut ℂ _ (star U) B).PosSemidef
    rw [Unitary.conjStarAlgAut_star_apply]
    exact hB.conjTranspose_mul_mul_same (U : Matrix n n ℂ)
  have h := E43_diagonal _ hX.eigenvalues_nonneg (f B) hB'
  change trace (((diagonal (RCLike.ofReal ∘ hX.isHermitian.eigenvalues)) ^ 4 * f B) ^ 3) ≤
    mean43 ((diagonal (RCLike.ofReal ∘ hX.isHermitian.eigenvalues)) ^ 3) (f B) at h
  have hd : f X = diagonal (RCLike.ofReal ∘ hX.isHermitian.eigenvalues) :=
    hX.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  rw [← hd, ← map_pow f, ← map_mul f, ← map_pow f, ← map_pow f,
    trace_conjugation] at h
  change _ ≤ mean43 (f.toAlgEquiv (X ^ 3)) (f.toAlgEquiv B) at h
  simpa only [mean43_map f.toAlgEquiv (trace_conjugation (star U))] using h

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- Hägele's refined BMV product bound with the positive spectral power A^(4/3). -/
theorem E43_all (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ (4 / 3 : ℝ)) * B) ^ 3) ≤ mean43 A B := by
  let X := A ^ (1 / 3 : ℝ)
  have hX : 0 ≤ X := CFC.rpow_nonneg
  have hpow (k : ℕ) : X ^ k = A ^ ((1 / 3 : ℝ) * k) := by
    rw [← CFC.rpow_natCast X k hX]
    exact CFC.rpow_rpow_of_exponent_nonneg A (1 / 3) k (by norm_num) (by positivity) hA.nonneg
  have h3 : X ^ (3 : ℕ) = A := by
    rw [hpow, show (1 / 3 : ℝ) * (↑(3 : ℕ) : ℝ) = 1 by norm_num, CFC.rpow_one A hA.nonneg]
  have h4 : X ^ (4 : ℕ) = A ^ (4 / 3 : ℝ) := by
    rw [hpow]
    congr 1
    norm_num
  simpa only [h3, h4] using E43_cubeRoot X B (Matrix.nonneg_iff_posSemidef.mp hX) hB

private theorem L43_fin {m : ℕ} (H K : Matrix (Fin m) (Fin m) ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((4 : ℝ) • H + (3 : ℝ) • K)) ≤ mean43 (exp H) (exp K) := by
  by_cases hm : m = 0
  · subst m
    simp [mean43, gapOrbits43, traceGaps43, trace_eq_zero_of_isEmpty]
  let _ : NeZero m := ⟨hm⟩
  let T : Matrix (Fin m) (Fin m) ℂ := (1 / 3 : ℝ) • H
  let X := exp T
  have hT : T.IsHermitian := hermitian_real_smul hH _
  have hScale : (3 : ℝ) • ((4 : ℝ) • T) = (4 : ℝ) • H := by
    dsimp only [T]
    rw [smul_smul, smul_smul]
    norm_num
  have hpow (k : ℕ) : X ^ k = exp ((k : ℝ) • T) := by
    rw [Nat.cast_smul_eq_nsmul, Matrix.exp_nsmul]
  have h3 : X ^ (3 : ℕ) = exp H := by
    rw [hpow]
    norm_num [T, smul_smul]
  have h4 : X ^ (4 : ℕ) = exp ((4 : ℝ) • T) := by simpa only [Nat.cast_ofNat] using hpow 4
  have hE := E43_cubeRoot X (exp K) (exp_posDef hT).posSemidef (exp_posDef hK).posSemidef
  rw [h3, h4] at hE
  have hh := hermitian_real_smul hT 4
  have ht := exponential_trace_le_cube ((4 : ℝ) • T) K hh hK
  rw [hScale] at ht
  refine le_trans ?_ hE
  refine Complex.le_def.mpr ⟨ht, ?_⟩
  have he : IsSelfAdjoint (trace (exp ((4 : ℝ) • H + (3 : ℝ) • K))) := by
    change star (trace _) = _
    rw [← trace_conjTranspose, ((hermitian_real_smul hH 4).add (hermitian_real_smul hK 3)).exp.eq]
  rw [(Complex.im_eq_zero_iff_isSelfAdjoint _).mpr he,
    (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
      (trace_cube_isSelfAdjoint _ _ hh.exp hK.exp)]

open scoped Matrix.Norms.Operator in
/-- The refined BMV exponential bound for any finite-dimensional Hermitian inputs. -/
theorem L43_all (H K : Matrix n n ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((4 : ℝ) • H + (3 : ℝ) • K)) ≤ mean43 (exp H) (exp K) := by
  let e := Fintype.equivFin n
  let f := Matrix.reindexAlgEquiv ℂ ℂ e
  have htr (A : Matrix n n ℂ) : trace (f A) = trace A := by
    change (∑ i, A (e.symm i) (e.symm i)) = ∑ i, A i i
    exact e.symm.sum_comp (fun i ↦ A i i)
  have hExp (A : Matrix n n ℂ) : f (exp A) = exp (f A) :=
    NormedSpace.map_exp f
      (continuous_matrix fun i j ↦ continuous_apply_apply (e.symm i) (e.symm j)) A
  have hSmul (r : ℝ) (A : Matrix n n ℂ) : f (r • A) = r • f A := rfl
  have hfH : (f H).IsHermitian := (isHermitian_submatrix_equiv e.symm).mpr hH
  have hfK : (f K).IsHermitian := (isHermitian_submatrix_equiv e.symm).mpr hK
  have h := L43_fin (f H) (f K) hfH hfK
  rw [← hSmul, ← hSmul, ← map_add f, ← hExp, htr, ← hExp, ← hExp, mean43_map f htr] at h
  exact h

#print axioms balancedWords43_count
#print axioms mean43_eq_enumerated
#print axioms E43_cubeRoot
#print axioms E43_all
#print axioms L43_all

end RefinedBMV
