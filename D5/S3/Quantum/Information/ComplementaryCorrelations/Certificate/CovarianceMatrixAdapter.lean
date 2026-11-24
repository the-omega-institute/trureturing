/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceMatrixAdapter
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceMatrixAdapter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Information/ComplementaryCorrelations/QubitQutritAnchorConvexity.qubit_qutrit_anchor_convexity; premises=D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.covariance_posSemidef
   digest: The Weyl covariance certificate gives the raw diagonal-circulant bound at the actual state square root. -/

import D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate.CovarianceCertificate
import D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate.CovarianceWeylMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.Data.ZMod.Basic

/-! The exact covariance matrix compressed to actual diagonal and circulant tests. -/

set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace QianACC.CovarianceMatrixAdapter

open CovarianceCertificate
open CovarianceWeylMatrix
open private entryWeights from D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate.CovarianceCertificateCore

/-- The homogeneous physical numerator, with same-basis and cross-basis weights. -/
def rawCov {n : Type*} [Fintype n] (T A B : Matrix n n ℂ) (same : Bool) : ℂ :=
  let N := (T * T).trace
  let P := (T * T * A * B).trace
  let Q := (T * T * B * A).trace
  let M := (T * A * T * B).trace
  let pq := (T * T * A).trace * (T * T * B).trace
  if same then N * ((3 / 2) * P + (3 / 2) * Q - 2 * M) - pq
  else N * ((5 / 4) * P - (1 / 4) * Q + M) - 2 * pq

private theorem rawCov_add_left (T A A' B : Mat) (s : Bool) :
    rawCov T (A + A') B s = rawCov T A B s + rawCov T A' B s := by
  cases s <;> simp only [rawCov, Bool.false_eq_true, ite_false, ite_true,
    Matrix.mul_add, Matrix.add_mul, Matrix.trace_add] <;> ring

private theorem rawCov_add_right (T A B B' : Mat) (s : Bool) :
    rawCov T A (B + B') s = rawCov T A B s + rawCov T A B' s := by
  cases s <;> simp only [rawCov, Bool.false_eq_true, ite_false, ite_true,
    Matrix.mul_add, Matrix.add_mul, Matrix.trace_add] <;> ring

private theorem rawCov_smul_left (T A B : Mat) (s : Bool) (c : ℂ) :
    rawCov T (c • A) B s = c * rawCov T A B s := by
  cases s <;> simp only [rawCov, Bool.false_eq_true, ite_false, ite_true,
    mul_smul_comm, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul] <;> ring

private theorem rawCov_smul_right (T A B : Mat) (s : Bool) (c : ℂ) :
    rawCov T A (c • B) s = c * rawCov T A B s := by
  cases s <;> simp only [rawCov, Bool.false_eq_true, ite_false, ite_true,
    mul_smul_comm, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul] <;> ring

private theorem rawCov_one_left (T B : Mat) (s : Bool) :
    rawCov T 1 B s = 0 := by
  cases s <;> simp [rawCov] <;> ring

private theorem rawCov_one_right (T A : Mat) (s : Bool) :
    rawCov T A 1 s = 0 := by
  cases s <;> simp [rawCov, Matrix.trace_mul_cycle T A T] <;> ring

private def slot (a : Test) : Fin 2 := if a.val < 2 then 0 else 1

private theorem sameSlot (a b : Test) : slot a = slot b ↔ a.val / 2 = b.val / 2 := by
  revert a b
  decide +kernel

private theorem covariance_entry (T : Mat) (a b : Test) :
    covarianceMatrix (coordinate T) a b =
      rawCov T (weyl (testWeight a))ᴴ (weyl (testWeight b)) (decide (slot a = slot b)) := by
  let c := negWeight (testWeight a)
  let d := testWeight b
  let tr := traceForm (coordinate T)
  have ht := reconstruct T
  have hN : tr (fun i j => [i, j]) = (T * T).trace := by
    simpa only [List.nil_append, List.cons_append, List.map_nil, List.prod_nil, Matrix.mul_one] using (trace_two _ [] [] T ht).symm
  have hP : tr (fun i j => [i, j, c, d]) = (T * T * weyl c * weyl d).trace := by
    simpa only [List.nil_append, List.cons_append, List.map_nil, List.map_cons, List.prod_nil, List.prod_cons, Matrix.mul_one,
      Matrix.mul_assoc] using (trace_two _ [] [c, d] T ht).symm
  have hQ : tr (fun i j => [i, j, d, c]) = (T * T * weyl d * weyl c).trace := by
    simpa only [List.nil_append, List.cons_append, List.map_nil, List.map_cons, List.prod_nil, List.prod_cons, Matrix.mul_one,
      Matrix.mul_assoc] using (trace_two _ [] [d, c] T ht).symm
  have hM : tr (fun i j => [i, c, j, d]) = (T * weyl c * T * weyl d).trace := by
    simpa only [List.nil_append, List.cons_append, List.map_nil, List.map_cons, List.prod_nil, List.prod_cons, Matrix.mul_one]
      using (trace_two _ [c] [d] T ht).symm
  have hp : tr (fun i j => [i, j, c]) = (T * T * weyl c).trace := by
    simpa only [List.nil_append, List.cons_append, List.map_nil, List.map_cons, List.prod_nil, List.prod_cons, Matrix.mul_one]
      using (trace_two _ [] [c] T ht).symm
  have hq : tr (fun i j => [i, j, d]) = (T * T * weyl d).trace := by
    simpa only [List.nil_append, List.cons_append, List.map_nil, List.map_cons, List.prod_nil, List.prod_cons, Matrix.mul_one]
      using (trace_two _ [] [d] T ht).symm
  rw [weyl_adjoint]
  change covarianceMatrix (coordinate T) a b = rawCov T (weyl c) (weyl d) _
  unfold covarianceMatrix
  dsimp only
  dsimp only [c, d, tr] at hN hP hQ hM hp hq
  rw [hN, hP, hQ, hM, hp, hq]
  by_cases h : a.val / 2 = b.val / 2
  · simp only [entryWeights, ite_eq_left h, sameSlot, h, decide_true, rawCov, ite_true]
    push_cast
    ring
  · simp only [entryWeights, ite_eq_right h, sameSlot, h, decide_false, rawCov,
      Bool.false_eq_true, ite_false]
    push_cast
    ring

private def compression (p : Test → ℂ) : Matrix Test (Fin 2) ℂ :=
  fun a k => if slot a = k then p a else 0

private def testMatrix (p : Test → ℂ) (k : Fin 2) : Mat :=
  ∑ a : Test, compression p a k • weyl (testWeight a)

private theorem rawCov_sum_left {ι : Type*} (S : Finset ι) (T B : Mat)
    (s : Bool) (A : ι → Mat) :
    rawCov T (∑ i ∈ S, A i) B s = ∑ i ∈ S, rawCov T (A i) B s := by
  classical
  induction S using Finset.induction_on with
  | empty => cases s <;> simp [rawCov]
  | insert a S ha ih => simp [Finset.sum_insert ha, rawCov_add_left, ih]

private theorem rawCov_sum_right {ι : Type*} (S : Finset ι) (T A : Mat)
    (s : Bool) (B : ι → Mat) :
    rawCov T A (∑ i ∈ S, B i) s = ∑ i ∈ S, rawCov T A (B i) s := by
  classical
  induction S using Finset.induction_on with
  | empty => cases s <;> simp [rawCov]
  | insert a S ha ih => simp [Finset.sum_insert ha, rawCov_add_right, ih]

private theorem compressed_entry (T : Mat) (p : Test → ℂ) (q : Fin 2 → ℂ)
    (i j : Fin 2) :
    let A := fun k => q k • (1 : Mat) + testMatrix p k
    rawCov T (A i)ᴴ (A j) (decide (i = j)) =
      ((compression p)ᴴ * covarianceMatrix (coordinate T) * compression p) i j := by
  dsimp only
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    rawCov_add_left, rawCov_add_right, rawCov_smul_left, rawCov_smul_right, rawCov_one_left,
    rawCov_one_right, mul_zero, zero_add, testMatrix, Matrix.conjTranspose_sum, rawCov_sum_left,
    rawCov_sum_right, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [covariance_entry]
  by_cases hi : slot a = i <;> by_cases hj : slot b = j
  all_goals simp [compression, hi, hj] <;> ring

/-- Positive semidefiniteness of the two actual physical tests. The square
root variable may be any Hermitian matrix, including zero. -/
theorem physical_posSemidef (T : Mat) (hT : T.IsHermitian) (d f : Fin 3 → ℂ)
    (hd : (Matrix.diagonal d).IsHermitian) (hf : (Matrix.circulant f).IsHermitian) :
    (Matrix.of fun i j : Fin 2 => rawCov T (![Matrix.diagonal d, Matrix.circulant f] i)
      (![Matrix.diagonal d, Matrix.circulant f] j) (decide (i = j))).PosSemidef := by
  let B : Fin 2 → Mat := ![Matrix.diagonal d, Matrix.circulant f]
  let p : Test → ℂ := ![coordinate (Matrix.diagonal d) 1, coordinate (Matrix.diagonal d) 2,
    f 1, f 2]
  let q : Fin 2 → ℂ := ![coordinate (Matrix.diagonal d) 0, f 0]
  have hB (i : Fin 2) : B i = q i • (1 : Mat) + testMatrix p i := by
    fin_cases i
    · simpa [B, p, q, testMatrix, compression, slot, testWeight, Fin.sum_univ_succ]
        using diagonal_expansion d
    · simpa [B, p, q, testMatrix, compression, slot, testWeight, Fin.sum_univ_succ]
        using circulant_expansion f
  have hH (i : Fin 2) : (B i).IsHermitian := by fin_cases i <;> assumption
  have heq : (Matrix.of fun i j => rawCov T (B i) (B j) (decide (i = j))) =
      (compression p)ᴴ * covarianceMatrix (coordinate T) * compression p := by
    ext i j : 1
    change rawCov T (B i) (B j) _ = _
    calc
      rawCov T (B i) (B j) (decide (i = j)) =
          rawCov T (B i)ᴴ (B j) (decide (i = j)) := by rw [(hH i).eq]
      _ = _ := by simpa only [← hB] using compressed_entry T p q i j
  change (Matrix.of fun i j => rawCov T (B i) (B j) (decide (i = j))).PosSemidef
  rw [heq]
  exact (covariance_posSemidef _ (coordinate_star hT)).conjTranspose_mul_mul_same _

private theorem trace_cycle_star {n : Type*} [Fintype n] {A B C : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    (A * C * B).trace = star (A * B * C).trace := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hA.eq, hB.eq, hC.eq, Matrix.trace_mul_cycle', Matrix.mul_assoc]

private theorem trace_real {n : Type*} [Fintype n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A * B).trace.im = 0 := by
  have h : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq,
      Matrix.trace_mul_comm]
  have hi := congrArg Complex.im h
  change -(A * B).trace.im = (A * B).trace.im at hi
  linarith

private theorem midpoint_real {n : Type*} [Fintype n] {T A B : Matrix n n ℂ}
    (hT : T.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (T * A * T * B).trace.im = 0 := by
  apply trace_real _ hB
  change (T * A * T)ᴴ = T * A * T
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hT.eq, hA.eq, Matrix.mul_assoc]

private theorem det_bound (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef) :
    (M 0 1).re ^ 2 + (M 0 1).im ^ 2 ≤ (M 0 0).re * (M 1 1).re := by
  have hd := (Complex.nonneg_iff.mp hM.det_nonneg).1
  rw [Matrix.det_fin_two] at hd
  have h10 : M 1 0 = star (M 0 1) := congrFun (congrFun hM.isHermitian.eq 1) 0 |>.symm
  have hii (i : Fin 2) : (M i i).im = 0 := by
    have hi := congrArg Complex.im (congrFun (congrFun hM.isHermitian.eq i) i)
    change -(M i i).im = (M i i).im at hi
    linarith
  rw [h10] at hd
  simp only [Complex.sub_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im, hii, mul_zero, sub_zero] at hd
  nlinarith only [hd]

section Raw

variable {n : Type*} [Fintype n]

/-- The density-normalized raw inequality consumed by the centered moment bound. -/
def RawBound (T b e : Matrix n n ℂ) : Prop :=
  let β := T * T
  let p := (β * b).trace.re
  let q := (β * e).trace.re
  ((β * b * e).trace.re + (T * b * T * e).trace.re - 2 * p * q) ^ 2 +
      (9 / 4 : ℝ) * (β * b * e).trace.im ^ 2 ≤
    (3 * (β * b * b).trace.re - 2 * (T * b * T * b).trace.re - p ^ 2) *
    (3 * (β * e * e).trace.re - 2 * (T * e * T * e).trace.re - q ^ 2)

private theorem raw_of_psd (T b e : Matrix n n ℂ) (hT : T.IsHermitian)
    (hb : b.IsHermitian) (he : e.IsHermitian) (hn : (T * T).trace = 1)
    (hp : (Matrix.of fun i j : Fin 2 => rawCov T (![b, e] i) (![b, e] j)
      (decide (i = j))).PosSemidef) : RawBound T b e := by
  have hβ : (T * T).IsHermitian := by
    change (T * T)ᴴ = T * T
    rw [Matrix.conjTranspose_mul, hT.eq]
  have hmeansb := trace_real hβ hb
  have hmeanse := trace_real hβ he
  have hmid := midpoint_real hT hb he
  change (T * T * b).trace.im = 0 at hmeansb
  change (T * T * e).trace.im = 0 at hmeanse
  change (T * b * T * e).trace.im = 0 at hmid
  have hcross := trace_cycle_star hβ hb he
  have h := det_bound _ hp
  change (rawCov T b e false).re ^ 2 + (rawCov T b e false).im ^ 2 ≤
    (rawCov T b b true).re * (rawCov T e e true).re at h
  simp only [rawCov, hn, hcross, Complex.star_def] at h
  norm_num [Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im] at h
  rw [hmeansb, hmeanse, hmid] at h
  unfold RawBound
  convert h using 1 <;> ring

end Raw

open scoped MatrixOrder in
private def toFin : Matrix (ZMod 3) (ZMod 3) ℂ ≃ₐ[ℂ] Mat :=
  Matrix.reindexAlgEquiv ℂ ℂ (ZMod.finEquiv 3).toEquiv.symm

private theorem toFin_hermitian {A : Matrix (ZMod 3) (ZMod 3) ℂ} (hA : A.IsHermitian) :
    (toFin A).IsHermitian := hA.submatrix _

private theorem toFin_diagonal (d : ZMod 3 → ℂ) :
    toFin (Matrix.diagonal d) = Matrix.diagonal (d ∘ ZMod.finEquiv 3) := by
  ext i j : 1
  change (Matrix.diagonal d) (ZMod.finEquiv 3 i) (ZMod.finEquiv 3 j) = _
  simp [Matrix.diagonal_apply, (ZMod.finEquiv 3).injective.eq_iff]

private theorem toFin_circulant (f : ZMod 3 → ℂ) :
    toFin (Matrix.circulant f) = Matrix.circulant (f ∘ ZMod.finEquiv 3) := by
  ext i j : 1
  change f (ZMod.finEquiv 3 i - ZMod.finEquiv 3 j) = f (ZMod.finEquiv 3 (i - j))
  rw [map_sub]

private theorem toFin_trace (A : Matrix (ZMod 3) (ZMod 3) ℂ) : (toFin A).trace = A.trace := by
  exact Fintype.sum_equiv (ZMod.finEquiv 3).toEquiv _ _ fun _ => rfl

/-- The covariance matrix on Bob's native `ZMod 3` indexing. -/
theorem bob_physical_posSemidef (T : Matrix (ZMod 3) (ZMod 3) ℂ) (hT : T.IsHermitian)
    (d f : ZMod 3 → ℂ) (hd : (Matrix.diagonal d).IsHermitian)
    (hf : (Matrix.circulant f).IsHermitian) :
    (Matrix.of fun i j : Fin 2 => rawCov T (![Matrix.diagonal d, Matrix.circulant f] i)
      (![Matrix.diagonal d, Matrix.circulant f] j) (decide (i = j))).PosSemidef := by
  have hd' := toFin_hermitian hd
  have hf' := toFin_hermitian hf
  rw [toFin_diagonal] at hd'
  rw [toFin_circulant] at hf'
  have h := physical_posSemidef (toFin T) (toFin_hermitian hT) _ _ hd' hf'
  have hinv (A B : Matrix (ZMod 3) (ZMod 3) ℂ) (s : Bool) :
      rawCov (toFin T) (toFin A) (toFin B) s = rawCov T A B s := by
    simp only [rawCov, ← map_mul, toFin_trace]
  have hentry (i : Fin 2) :
      toFin (![Matrix.diagonal d, Matrix.circulant f] i) =
        ![Matrix.diagonal (d ∘ ZMod.finEquiv 3), Matrix.circulant (f ∘ ZMod.finEquiv 3)] i := by
    fin_cases i
    · exact toFin_diagonal d
    · exact toFin_circulant f
  have heq :
      (Matrix.of fun i j : Fin 2 => rawCov T (![Matrix.diagonal d, Matrix.circulant f] i)
        (![Matrix.diagonal d, Matrix.circulant f] j) (decide (i = j))) =
      (Matrix.of fun i j : Fin 2 => rawCov (toFin T)
        (![Matrix.diagonal (d ∘ ZMod.finEquiv 3), Matrix.circulant (f ∘ ZMod.finEquiv 3)] i)
        (![Matrix.diagonal (d ∘ ZMod.finEquiv 3), Matrix.circulant (f ∘ ZMod.finEquiv 3)] j)
        (decide (i = j))) := by
    ext i j : 1
    simp only [Matrix.of_apply, ← hentry, hinv]
  rw [heq]
  exact h

/-- The raw covariance inequality on the actual Hermitian square root of a
trace-one qutrit state. The observable means are taken in that state. -/
theorem bob_raw_covariance (β : Matrix (ZMod 3) (ZMod 3) ℂ)
    (hβ : β.PosSemidef) (htr : β.trace = 1)
    (d f : ZMod 3 → ℂ) (hd : (Matrix.diagonal d).IsHermitian)
    (hf : (Matrix.circulant f).IsHermitian) :
    let T := CFC.sqrt β
    let b := Matrix.diagonal d
    let e := Matrix.circulant f
    let p := (β * b).trace.re
    let q := (β * e).trace.re
    ((β * b * e).trace.re + (T * b * T * e).trace.re - 2 * p * q) ^ 2 +
        (9 / 4 : ℝ) * (β * b * e).trace.im ^ 2 ≤
      (3 * (β * b * b).trace.re - 2 * (T * b * T * b).trace.re - p ^ 2) *
      (3 * (β * e * e).trace.re - 2 * (T * e * T * e).trace.re - q ^ 2) := by
  let T := CFC.sqrt β
  have hT : T.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg β)).isHermitian
  have hs : T * T = β := CFC.sqrt_mul_sqrt_self β hβ.nonneg
  have hn : (T * T).trace = 1 := hs ▸ htr
  have h := raw_of_psd T _ _ hT hd hf hn (bob_physical_posSemidef T hT d f hd hf)
  simpa only [RawBound, hs] using h

end QianACC.CovarianceMatrixAdapter
