/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteDifferential
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteDifferential
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Kronecker]
   utility: none
   digest: Periodic two-site marginal differential on a binary bond-two chart. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.Algebra.CharP.Lemmas

/-! The two-site partial trace is a transfer contraction with a finite-field rank certificate. -/

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteDifferential

open Matrix

set_option maxHeartbeats 1000000
open scoped BigOperators Matrix Kronecker ComplexConjugate
open PeriodicMPSParentIntersection (Bond Word twoFlattening)
open UniformMPSExpectedDimensionRefutation (traceWord)

private abbrev Bits := Fin 2 × Fin 2
private abbrev Entries := Bits × Bits
private abbrev Direction := Fin 4 × Fin 2

private def tensors {R : Type*} [Zero R] [One R] (a : R) (x : Fin 4 → R) :
    Fin 2 → Matrix (Fin 2) (Fin 2) R :=
  ![!![a, 0; 0, x 0], !![x 1, 1; x 2, x 3]]

noncomputable section

/-- The affine chart with fixed first diagonal entry and unit upper-right entry. -/
def chart (a : ℂ) (x : Fin 4 → ℂ) : Fin 2 → Bond := tensors a x

/-- The actual unnormalized two-site density matrix on the periodic ring of length r+4. -/
def rawTwo (A : Fin 2 → Bond) (r : ℕ) : Matrix Bits Bits ℂ :=
  twoFlattening A r * (twoFlattening A r).conjTranspose

private def along (x : Fin 4 → ℂ) (d : Direction) (t : ℝ) (j : Fin 4) : ℂ :=
  x j + if j = d.1 then (t : ℂ) * (if d.2 = 0 then 1 else Complex.I) else 0

/-- The value column followed by the eight real partial derivatives of the raw marginal. -/
def augmented (r : ℕ) (a : ℂ) (x : Fin 4 → ℂ) : Matrix Entries (Fin 9) ℂ :=
  fun p => Fin.cases (rawTwo (chart a x) r p.1 p.2)
    (fun d => deriv (fun t : ℝ =>
      rawTwo (chart a (along x (finProdFinEquiv.symm d) t)) r p.1 p.2) 0)

end

private def pairBlock {R : Type*} [Mul R]
    (A B : Fin 2 → Matrix (Fin 2) (Fin 2) R) (i j : Fin 2) :
    Matrix Bits Bits R := A i ⊗ₖ B j

private def transfer {R : Type*} [Add R] [Mul R]
    (A B : Fin 2 → Matrix (Fin 2) (Fin 2) R) : Matrix Bits Bits R :=
  pairBlock A B 0 0 + pairBlock A B 1 1

private def contraction {R : Type*} [CommSemiring R]
    (A B : Fin 2 → Matrix (Fin 2) (Fin 2) R) (m : ℕ) (p : Entries) : R :=
  (pairBlock A B p.1.1 p.2.1 * pairBlock A B p.1.2 p.2.2 * transfer A B ^ m).trace

private lemma transfer_pow {R : Type*} [CommSemiring R]
    (A B : Fin 2 → Matrix (Fin 2) (Fin 2) R) (m : ℕ) :
    transfer A B ^ m =
      ∑ w : Word m,
        (List.ofFn (fun i => A (w i))).prod ⊗ₖ (List.ofFn (fun i => B (w i))).prod := by
  induction m with
  | zero => simp [Finset.univ_unique, Matrix.one_kronecker_one]
  | succ m ih =>
    rw [pow_succ', ih, ← (Fin.consEquiv (fun _ : Fin (m+1) => Fin 2)).sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons,
      Fin.sum_univ_two]
    unfold transfer pairBlock
    simp_rw [Matrix.mul_kronecker_mul, ← Finset.mul_sum, ← add_mul]

private lemma traceWord_cons_cons (A : Fin 2 → Bond) (m : ℕ) (p : Bits) (w : Word m) :
    traceWord 2 2 (2 + m) A (Fin.append ![p.1, p.2] w) =
      (A p.1 * A p.2 * (List.ofFn (fun i => A (w i))).prod).trace := by
  simp [traceWord, List.ofFn_comp', List.ofFn_fin_append, List.prod_append, List.ofFn_succ,
    Matrix.mul_assoc]

private lemma rawTwo_contraction (A : Fin 2 → Bond) (r : ℕ) (p : Entries) :
    rawTwo A r p.1 p.2 =
      contraction A (fun i => (A i).map (starRingEnd ℂ)) (r + 2) p := by
  classical
  rw [contraction, transfer_pow, Matrix.mul_sum, Matrix.trace_sum]
  simp only [rawTwo, Matrix.mul_apply, Matrix.conjTranspose_apply, twoFlattening,
    traceWord_cons_cons]
  apply Finset.sum_congr rfl
  intro w _
  simp only [pairBlock, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  congr 1
  let f : Bond →+* Bond := RingHom.mapMatrix (starRingEnd ℂ)
  change starRingEnd ℂ _ = (f (A p.2.1) * f (A p.2.2) *
    (List.ofFn fun i => f (A (w i))).prod).trace
  have hw : (List.ofFn fun i => f (A (w i))) =
      (List.ofFn fun i => A (w i)).map f := List.map_ofFn.symm
  rw [hw, ← map_list_prod, ← map_mul, ← map_mul]
  exact AddMonoidHom.map_trace (starRingEnd ℂ) _

private lemma map_contraction {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (A B : Fin 2 → Matrix (Fin 2) (Fin 2) R) (m : ℕ) (p : Entries) :
    f (contraction A B m p) =
      contraction (fun i => (A i).map f) (fun i => (B i).map f) m p := by
  let fm : Matrix Bits Bits R →+* Matrix Bits Bits S := RingHom.mapMatrix f
  have hK (i j : Fin 2) :
      fm (pairBlock A B i j) = pairBlock (fun i => (A i).map f) (fun i => (B i).map f) i j := by
    ext u v
    exact f.map_mul _ _
  simp only [contraction, AddMonoidHom.map_trace f]
  change (fm (_ * _ * _ ^ _)).trace = _
  simp only [map_mul, map_pow, transfer, map_add, hK]

private lemma map_tensors {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (a : R) (x : Fin 4 → R) (i : Fin 2) :
    (tensors a x i).map f = tensors (f a) (fun j => f (x j)) i := by
  ext u v
  fin_cases i <;> fin_cases u <;> fin_cases v <;> simp [tensors]

open Polynomial TrivSqZeroExt

private abbrev G := GaussianInt
private abbrev F := ZMod 13

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

private def imaginary : G := ⟨0, 1⟩

private lemma minus_one_not_square (z : ℤ) : (-1 : ℤ) ≠ z * z := by
  have h := mul_self_nonneg z
  omega


private def residue : G →+* F := Zsqrtd.lift ⟨5, by decide⟩
private noncomputable def complex : G →+* ℂ := Zsqrtd.lift ⟨Complex.I, by simp⟩

private lemma complex_star (z : G) : complex (star z) = conj (complex z) := by
  rcases z with ⟨a, b⟩
  simp [complex, Zsqrtd.lift_apply_apply, Zsqrtd.star_mk]

private def axis (d : Direction) (j : Fin 4) : G :=
  if j = d.1 then if d.2 = 0 then 1 else imaginary else 0

private lemma complex_axis (d : Direction) (j : Fin 4) :
    complex (axis d j) = if j = d.1 then (if d.2 = 0 then 1 else Complex.I) else 0 := by
  by_cases h : j = d.1 <;> by_cases k : d.2 = 0 <;>
    simp [axis, h, k, complex, imaginary, Zsqrtd.lift_apply_apply]

private noncomputable def lines (a : G) (x : Fin 4 → G) (d : Direction) :
    Fin 2 → Matrix (Fin 2) (Fin 2) (Polynomial G) :=
  tensors (C a) (fun j => C (x j) + X * C (axis d j))

private noncomputable def conjugateLines (a : G) (x : Fin 4 → G) (d : Direction) :
    Fin 2 → Matrix (Fin 2) (Fin 2) (Polynomial G) :=
  tensors (C (star a)) (fun j => C (star (x j)) + X * C (star (axis d j)))

private noncomputable def marginalLine (a : G) (x : Fin 4 → G) (d : Direction) (m : ℕ) (p : Entries) :
    Polynomial G :=
  contraction (lines a x d) (conjugateLines a x d) m p

private lemma evaluate_marginalLine (a : G) (x : Fin 4 → G) (d : Direction)
    (r : ℕ) (p : Entries) (t : ℝ) :
    (marginalLine a x d (r + 2) p).eval₂ complex (t : ℂ) =
      rawTwo (chart (complex a) (along (fun j => complex (x j)) d t)) r p.1 p.2 := by
  rw [rawTwo_contraction]
  change (eval₂RingHom complex (t : ℂ)) (marginalLine a x d (r + 2) p) = _
  rw [marginalLine, map_contraction]
  have h (j : Fin 4) : complex (x j) + (t : ℂ) * complex (axis d j) =
      along (fun j => complex (x j)) d t j := by
    by_cases hj : j = d.1 <;> simp [along, complex_axis, hj]
  have hstar (j : Fin 4) : complex (star (x j)) + (t : ℂ) * complex (star (axis d j)) =
      starRingEnd ℂ (along (fun j => complex (x j)) d t j) := by
    rw [← h j, map_add, map_mul]
    simp only [complex_star, Complex.conj_ofReal]
  conv_lhs => simp only [lines, conjugateLines, map_tensors]
  conv_rhs => simp only [chart, map_tensors]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_add, eval₂_mul, eval₂_X, h, complex_star]
  have hconj (j : Fin 4) :
      starRingEnd ℂ (complex (x j)) + (t : ℂ) * starRingEnd ℂ (complex (axis d j)) =
        starRingEnd ℂ (along (fun j => complex (x j)) d t j) := by simpa only [complex_star] using hstar j
  simp only [hconj]

private abbrev firstDirection : Direction := (0, 0)

private noncomputable def gaussianAugmented (a : G) (x : Fin 4 → G) (m : ℕ) :
    Matrix Entries (Fin 9) G :=
  fun p => Fin.cases ((marginalLine a x firstDirection m p).coeff 0)
    (fun d => (marginalLine a x (finProdFinEquiv.symm d) m p).coeff 1)

private lemma complex_augmented (a : G) (x : Fin 4 → G) (r : ℕ) :
    (gaussianAugmented a x (r + 2)).map complex =
      augmented r (complex a) (fun j => complex (x j)) := by
  ext p k
  refine Fin.cases ?_ (fun d => ?_) k
  · have h := evaluate_marginalLine a x firstDirection r p 0
    have hzero : along (fun j => complex (x j)) firstDirection 0 = fun j => complex (x j) := by
      funext j
      by_cases hj : j = firstDirection.1 <;> simp [along, hj]
    simpa [gaussianAugmented, augmented, hzero, eval₂_eq_eval_map,
      ← coeff_zero_eq_eval_zero] using h
  · let q := marginalLine a x (finProdFinEquiv.symm d) (r + 2) p
    have heval : (fun t : ℝ => (q.map complex).eval (t : ℂ)) =
        fun t : ℝ => rawTwo (chart (complex a)
          (along (fun j => complex (x j)) (finProdFinEquiv.symm d) t)) r p.1 p.2 := by
      funext t
      rw [← eval₂_eq_eval_map, evaluate_marginalLine]
    have h : HasDerivAt (fun t : ℂ => (q.map complex).eval t)
        (complex (q.coeff 1)) ((0 : ℝ) : ℂ) := by
      simpa [← coeff_zero_eq_eval_zero, coeff_derivative] using (q.map complex).hasDerivAt 0
    simpa only [gaussianAugmented, augmented, Matrix.map_apply, Fin.cases_succ, heval] using
      (h.comp_ofReal).deriv.symm

private def dualEval {R : Type*} [CommRing R] (f : G →+* R) : Polynomial G →+* DualNumber R :=
  eval₂RingHom ((inlHom R R).comp f) DualNumber.eps

private lemma dual_coeff {R : Type*} [CommRing R] (f : G →+* R) (q : Polynomial G) :
    (dualEval f q).fst = f (q.coeff 0) ∧ (dualEval f q).snd = f (q.coeff 1) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, fst_add, snd_add, coeff_add, hp.1, hp.2, hq.1, hq.2, and_self]
  | monomial n a =>
      rcases n with _ | _ | n
      · simp [dualEval]
      · simp [dualEval, ← C_mul_X_pow_eq_monomial]
      · have he : (DualNumber.eps : DualNumber R) ^ (n + 2) = 0 := by
          rw [pow_add, DualNumber.eps_pow_two, mul_zero]
        simp [dualEval, ← C_mul_X_pow_eq_monomial, coeff_monomial, he, Nat.succ_ne_zero,
          Nat.succ_inj]

private def dualTensors {R : Type*} [CommRing R] (f : G →+* R)
    (a : G) (x : Fin 4 → G) (d : Direction) :
    Fin 2 → Matrix (Fin 2) (Fin 2) (DualNumber R) :=
  tensors (R := DualNumber R) ⟨f a, 0⟩ (fun j => ⟨f (x j), f (axis d j)⟩)

private def dualContraction (a : G) (x : Fin 4 → G) (d : Direction) (m : ℕ) (p : Entries) :
    DualNumber F :=
  contraction (R := DualNumber F) (dualTensors residue a x d)
    (dualTensors (residue.comp (starRingEnd G)) a x d) m p

private lemma dual_marginalLine (f : G →+* F)
    (a : G) (x : Fin 4 → G) (d : Direction) (m : ℕ) (p : Entries) :
    dualEval f (marginalLine a x d m p) =
      contraction (R := DualNumber F) (dualTensors f a x d)
        (dualTensors (f.comp (starRingEnd G)) a x d) m p := by
  rw [marginalLine, map_contraction]
  have h (u v : G) :
      dualEval f (C u + X * C v) = ⟨f u, f v⟩ := by
    apply TrivSqZeroExt.ext <;> simp [dualEval]
  have hc (u : G) : dualEval f (C u) = ⟨f u, 0⟩ := by
    simp [dualEval]
    rfl
  simp only [lines, conjugateLines, map_tensors, dualTensors, h, hc,
    RingHom.comp_apply, starRingEnd_apply]

private def residueAugmented (a : G) (x : Fin 4 → G) (m : ℕ) :
    Matrix Entries (Fin 9) F :=
  fun p => Fin.cases (dualContraction a x firstDirection m p).fst
    (fun d => (dualContraction a x (finProdFinEquiv.symm d) m p).snd)

private lemma residue_augmented (a : G) (x : Fin 4 → G) (m : ℕ) :
    (gaussianAugmented a x m).map residue = residueAugmented a x m := by
  have h (d : Direction) (p : Entries) :
      dualEval residue (marginalLine a x d m p) = dualContraction a x d m p :=
    dual_marginalLine residue a x d m p
  apply Matrix.ext
  intro p k
  refine Fin.cases ?_ (fun d => ?_) k
  · exact (dual_coeff residue (marginalLine a x firstDirection m p)).1.symm.trans
      (congrArg (TrivSqZeroExt.fst : DualNumber F → F) (h firstDirection p))
  · let u : Direction := finProdFinEquiv.symm d
    exact (dual_coeff residue (marginalLine a x u m p)).2.symm.trans
      (congrArg (TrivSqZeroExt.snd : DualNumber F → F) (h u p))

private def point (i : Fin 4) : Fin 5 → G :=
  ![![⟨0,-2⟩, ⟨3,-1⟩, ⟨1,-6⟩, ⟨5,-1⟩, ⟨1,-1⟩],
    ![⟨2,-6⟩, ⟨0,-5⟩, ⟨4,6⟩, ⟨-2,4⟩, ⟨3,1⟩],
    ![⟨3,-3⟩, ⟨6,2⟩, ⟨1,3⟩, ⟨0,5⟩, ⟨-5,-5⟩],
    ![⟨4,0⟩, ⟨4,5⟩, ⟨0,0⟩, ⟨-3,-6⟩, ⟨0,4⟩]] i

private abbrev firstEntry (i : Fin 4) := point i 0
private abbrev variableEntries (i : Fin 4) (j : Fin 4) := point i j.succ

private abbrev leftTensors (i : Fin 4) (d : Direction) :
    Fin 2 → Matrix (Fin 2) (Fin 2) (DualNumber F) :=
  dualTensors residue (firstEntry i) (variableEntries i) d

private abbrev rightTensors (i : Fin 4) (d : Direction) :
    Fin 2 → Matrix (Fin 2) (Fin 2) (DualNumber F) :=
  dualTensors (residue.comp (starRingEnd G)) (firstEntry i) (variableEntries i) d

private def T (i : Fin 4) (d : Direction) : Matrix Bits Bits (DualNumber F) :=
  transfer (R := DualNumber F) (leftTensors i d) (rightTensors i d)

private abbrev Stored (R : Type) (n : ℕ) := Vector (Vector R n) n

private def store {R : Type} {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Stored R n :=
  Vector.ofFn fun i => Vector.ofFn fun j => A i j

private lemma vectorGetOfFn {R : Type} {n : ℕ} (f : Fin n → R) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = f i
  rw [Vector.getElem_ofFn]

private def entries {R : Type} {n : ℕ} (A : Stored R n) : Matrix (Fin n) (Fin n) R :=
  fun i j => (A.get i).get j

@[simp] private lemma entries_store {R : Type} {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    entries (store A) = A := by
  apply Matrix.ext
  intro i j
  change ((Vector.ofFn fun u => Vector.ofFn fun v => A u v).get i).get j = _
  rw [vectorGetOfFn, vectorGetOfFn]

private def toBits : Fin 4 ≃ Bits := (finProdFinEquiv (m := 2) (n := 2)).symm

private def read4 (A : Stored (DualNumber F) 4) : Matrix Bits Bits (DualNumber F) :=
  (Matrix.reindexRingEquiv (DualNumber F) toBits) (entries A)

private def pack4 (A : Matrix Bits Bits (DualNumber F)) : Stored (DualNumber F) 4 :=
  store (A.submatrix toBits toBits)

@[simp] private lemma read4_pack4 (A : Matrix Bits Bits (DualNumber F)) :
    read4 (pack4 A) = A := by
  apply Matrix.ext
  intro i j
  change entries (store (A.submatrix toBits toBits)) (toBits.symm i) (toBits.symm j) = A i j
  simp [Matrix.submatrix_apply]

private def mul4 (A B : Stored (DualNumber F) 4) : Stored (DualNumber F) 4 :=
  store (R := DualNumber F) fun i j =>
    entries A i 0 * entries B 0 j + entries A i 1 * entries B 1 j +
    entries A i 2 * entries B 2 j + entries A i 3 * entries B 3 j

@[simp] private lemma read4_mul4 (A B : Stored (DualNumber F) 4) :
    read4 (mul4 A B) = read4 A * read4 B := by
  rw [read4, read4, read4, ← map_mul]
  apply congrArg (Matrix.reindexRingEquiv (DualNumber F) toBits)
  exact (entries_store (R := DualNumber F) _).trans (Matrix.ext fun i j =>
    (Fin.sum_univ_four (M := DualNumber F) (fun k => entries A i k * entries B k j)).symm)

private def power4 (A : Stored (DualNumber F) 4) (m : ℕ) : ℕ → Stored (DualNumber F) 4
  | 0 => pack4 1
  | k + 1 =>
    let b := power4 (mul4 A A) (m / 2) k
    if m % 2 = 0 then b else mul4 b A

private lemma read4_power4 (A : Stored (DualNumber F) 4) (m k : ℕ) (h : m < 2 ^ k) :
    read4 (power4 A m k) = (read4 A) ^ m := by
  induction k generalizing A m with
  | zero =>
    have : m = 0 := by simpa using h
    simp [power4, this]
  | succ k ih =>
    have hk : m / 2 < 2 ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [pow_succ] using h
    have hmod := Nat.mod_add_div m 2
    simp only [power4]
    split
    · simp only [ih _ _ hk, read4_mul4, ← pow_two, ← pow_mul]
      congr 1
      omega
    · simp only [read4_mul4, ih _ _ hk, ← pow_two, ← pow_mul, ← pow_succ]
      congr 1
      omega

private def evalPower (i : Fin 4) (d : Direction) (m : ℕ) :=
  power4 (pack4 (T i d)) m 8

private lemma evalPower_correct (i : Fin 4) (d : Direction) (m : ℕ) (h : m < 256) :
    read4 (evalPower i d m) = T i d ^ m :=
  (read4_power4 _ _ _ h).trans (by rw [read4_pack4])

private def fstRing : DualNumber F →+* F := (TrivSqZeroExt.fstHom F F F).toRingHom

private lemma square_zero_of_fst_zero (A : Matrix Bits Bits (DualNumber F))
    (h : RingHom.mapMatrix fstRing A = 0) : A * A = 0 := by
  have hz (i j : Bits) : (A i j).fst = 0 := by
    exact congrFun (congrFun h i) j
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply TrivSqZeroExt.ext
  · simp [hz]
  · simp [DualNumber.snd_mul, hz]

local instance : CharP (DualNumber F) 13 where
  cast_eq_zero_iff n := by
    change (n : DualNumber F) = 0 ↔ 13 ∣ n
    constructor
    · intro h
      exact (CharP.cast_eq_zero_iff F 13 n).mp (by simpa [fstRing] using congrArg fstRing h)
    · intro h
      have hn := (CharP.cast_eq_zero_iff F 13 n).mpr h
      apply TrivSqZeroExt.ext
      · simpa [fstRing] using hn
      · simp

private lemma lift_transfer_period (A : Matrix Bits Bits (DualNumber F))
    (h : (RingHom.mapMatrix fstRing A) ^ 16 = (RingHom.mapMatrix fstRing A) ^ 4) :
    A ^ 164 = A ^ 8 := by
  let B : Matrix Bits Bits (DualNumber F) := A ^ 12 - 1
  have hb : RingHom.mapMatrix fstRing (A ^ 4 * B) = 0 := by
    simp only [B, map_mul, map_sub, map_one, map_pow, mul_sub, mul_one, ← pow_add]
    exact sub_eq_zero.mpr h
  have hc : Commute (A ^ 4) B :=
    ((Commute.refl A).pow_pow 4 12).sub_right (Commute.one_right _)
  have h2 : A ^ 8 * B ^ 2 = 0 := by
    simpa only [← pow_two, hc.mul_pow, ← pow_mul] using
      square_zero_of_fst_zero (A ^ 4 * B) hb
  have h13 : A ^ 8 * B ^ 13 = 0 := by
    have hp : B ^ 13 = B ^ 2 * B ^ 11 := pow_add B 2 11
    rw [hp, ← mul_assoc, h2, zero_mul]
  have hf : B ^ 13 = A ^ 156 - 1 := by
    have hcomm : Commute (A ^ 12) (1 : Matrix Bits Bits (DualNumber F)) :=
      Commute.one_right _
    calc
      B ^ 13 = (A ^ 12) ^ 13 - (1 : Matrix Bits Bits (DualNumber F)) ^ 13 :=
        sub_pow_char_of_commute 13 hcomm
      _ = A ^ 156 - 1 := by rw [← pow_mul, one_pow]
  rw [hf, mul_sub, mul_one, ← pow_add] at h13
  exact sub_eq_zero.mp h13

private lemma fst_transfer (i : Fin 4) (d : Direction) :
    RingHom.mapMatrix fstRing (T i d) = RingHom.mapMatrix fstRing (T i firstDirection) := by
  apply Matrix.ext
  intro u v
  have hf (f : G →+* F) (e : Direction) (j : Fin 2) :
      (dualTensors f (firstEntry i) (variableEntries i) e j).map fstRing =
      tensors (f (firstEntry i)) (fun k => f (variableEntries i k)) j := by
    exact map_tensors (R := DualNumber F) (S := F) fstRing
      (⟨f (firstEntry i), 0⟩ : DualNumber F)
      (fun k => (⟨f (variableEntries i k), f (axis e k)⟩ : DualNumber F)) j
  have hh (f : G →+* F) (j : Fin 2) :
      (dualTensors f (firstEntry i) (variableEntries i) d j).map fstRing =
      (dualTensors f (firstEntry i) (variableEntries i) firstDirection j).map fstRing :=
    (hf f d j).trans (hf f firstDirection j).symm
  change fstRing (T i d u v) = fstRing (T i firstDirection u v)
  simp only [T, transfer, Matrix.add_apply, pairBlock, Matrix.kroneckerMap_apply, map_add, map_mul]
  congr 1 <;> congr 1 <;>
    first
    | exact congrFun (congrFun (hh residue _) _) _
    | exact congrFun (congrFun (hh (residue.comp (starRingEnd G)) _) _) _

private def baseCheck (i : Fin 4) : Bool :=
  let a := evalPower i firstDirection 16
  let b := evalPower i firstDirection 4
  (List.finRange 4).all fun u => (List.finRange 4).all fun v =>
    (entries a u v).fst.val == (entries b u v).fst.val

private lemma base_period_sound (i : Fin 4) (h : baseCheck i = true) :
    (RingHom.mapMatrix fstRing (T i firstDirection)) ^ 16 =
      (RingHom.mapMatrix fstRing (T i firstDirection)) ^ 4 := by
  rw [← map_pow, ← map_pow, ← evalPower_correct i firstDirection 16 (by decide),
    ← evalPower_correct i firstDirection 4 (by decide)]
  apply Matrix.ext
  intro u v
  unfold baseCheck at h
  exact ZMod.val_injective _ (beq_iff_eq.mp
    ((List.all_eq_true.mp (List.all_eq_true.mp h (toBits.symm u) (by simp)))
      (toBits.symm v) (by simp)))

private lemma period_from_base (h : ∀ i, baseCheck i = true) (i : Fin 4) (d : Direction) :
    T i d ^ 164 = T i d ^ 8 := by
  apply lift_transfer_period
  rw [fst_transfer]
  exact base_period_sound i (h i)

private def lowerBlock (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    Matrix (Fin n) (Fin n) F :=
  fun i j => A 0 0 * A i.succ j.succ - A i.succ 0 * A 0 j.succ

private def pivotCheck : (n : ℕ) → Stored F n → Bool
  | 0, _ => true
  | n + 1, A =>
    ((entries A 0 0).val != 0) && pivotCheck n (store (lowerBlock (entries A)))

private lemma pivotCheck_sound (n : ℕ) (A : Stored F n) (h : pivotCheck n A = true) :
    ∀ v, entries A *ᵥ v = 0 → v = 0 := by
  induction n with
  | zero => intro v _; funext j; exact Fin.elim0 j
  | succ n ih =>
    obtain ⟨hp, hs⟩ := Bool.and_eq_true_iff.mp h
    have hp' : entries A 0 0 ≠ 0 := by
      intro he
      simp [he] at hp
    intro v hv
    let M := entries A
    have row (i : Fin (n + 1)) :
        M i 0 * v 0 + ∑ j : Fin n, M i j.succ * v j.succ = 0 := by
      simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hv i
    have htail : (fun j : Fin n => v j.succ) = 0 := by
      apply ih (store (lowerBlock M)) hs
      funext i
      simp only [entries_store, Matrix.mulVec, dotProduct, lowerBlock, Pi.zero_apply]
      simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
      linear_combination M 0 0 * row i.succ - M i.succ 0 * row 0
    have hv0 : v 0 = 0 := by
      have hz (j : Fin n) : v j.succ = 0 := congrFun htail j
      simp only [hz, mul_zero, Finset.sum_const_zero, add_zero] at row
      exact (mul_eq_zero.mp (row 0)).resolve_left hp'
    funext j
    exact Fin.cases hv0 (congrFun htail) j

private lemma pivotCheck_det (n : ℕ) (A : Matrix (Fin n) (Fin n) F)
    (h : pivotCheck n (store A) = true) : A.det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det A).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hzero := pivotCheck_sound n (store A) h (x - y)
  simpa [Matrix.mulVec_sub, hxy, sub_eq_zero] using hzero

private def rowsOf (packed : ℕ) (i : Fin 9) : Entries :=
  let pair := (finProdFinEquiv (m := 4) (n := 4)).symm (Fin.ofNat 16 (packed / 16 ^ i.val))
  (toBits pair.1, toBits pair.2)

private def checkedMinor (m : ℕ) (i : Fin 4) (packed : ℕ) : Stored F 9 :=
  let powers := Vector.ofFn fun d : Fin 8 => evalPower i (finProdFinEquiv.symm d) m
  store fun u k =>
    let p := rowsOf packed u
    let coefficient (d : Fin 8) :=
      let dir := finProdFinEquiv.symm d
      let A := leftTensors i dir
      let B := rightTensors i dir
      let front := mul4 (pack4 (pairBlock A B p.1.1 p.2.1)) (pack4 (pairBlock A B p.1.2 p.2.2))
      let product := mul4 front (powers.get d)
      entries product 0 0 + entries product 1 1 + entries product 2 2 + entries product 3 3
    Fin.cases (coefficient 0).fst (fun d => (coefficient d).snd) k

private lemma checkedMinor_correct (m : ℕ) (i : Fin 4) (packed : ℕ) (hm : m < 256) :
    entries (checkedMinor m i packed) =
      (residueAugmented (firstEntry i) (variableEntries i) m).submatrix (rowsOf packed) id := by
  have htrace (A : Stored (DualNumber F) 4) :
      entries A 0 0 + entries A 1 1 + entries A 2 2 + entries A 3 3 = (read4 A).trace := by
    have hsum : (∑ j : Fin 4, entries A j j) =
        ∑ j : Bits, entries A (toBits.symm j) (toBits.symm j) := by
      rw [← toBits.sum_comp]
      simp only [Equiv.symm_apply_apply]
    have h4 := Fin.sum_univ_four (M := DualNumber F) (fun j => entries A j j)
    have hh : (∑ j : Bits, entries A (toBits.symm j) (toBits.symm j)) =
        (read4 A).trace := rfl
    exact h4.symm.trans (hsum.trans hh)
  have hvalue (u : Fin 9) (d : Fin 8) :
      let p := rowsOf packed u
      let dir := finProdFinEquiv.symm d
      let A := leftTensors i dir
      let B := rightTensors i dir
      let front := mul4 (pack4 (pairBlock A B p.1.1 p.2.1)) (pack4 (pairBlock A B p.1.2 p.2.2))
      (read4 (mul4 front (evalPower i dir m))).trace =
        dualContraction (firstEntry i) (variableEntries i) dir m p := by
    dsimp only
    rw [read4_mul4, read4_mul4, read4_pack4, read4_pack4, evalPower_correct _ _ _ hm]
    rfl
  unfold checkedMinor
  refine (entries_store (R := F) _).trans ?_
  apply Matrix.ext
  intro u k
  simp only [vectorGetOfFn, htrace, hvalue, Matrix.submatrix_apply, id]
  refine Fin.cases ?_ (fun d => ?_) k <;> rfl

/-- The selected point and nine row indices in pivot order for each complement length
from 2 through 163. Each row occupies four bits, in increasing pivot order. -/
private def certificates : Vector (Fin 4 × ℕ) 162 := #v[
  (0, 0xdc7654310), (0, 0xdc7653410), (0, 0xdc7654310), (1, 0xdc7546310),
  (1, 0xdc7654301), (1, 0xdc7654310), (0, 0xdc7653410), (0, 0xdc7654310),
  (0, 0xdc6574310), (1, 0xdc7654310), (1, 0xdc7654301), (1, 0xbdc564310),
  (0, 0xdc7654310), (0, 0xdc7643250), (0, 0xdc7654310), (1, 0xdc7654310),
  (1, 0xdc7653401), (1, 0xdc7654310), (0, 0xdc7653410), (0, 0xdc7653410),
  (0, 0xdc7654310), (1, 0xdc7654310), (1, 0xdc7654301), (1, 0xfc7635410),
  (0, 0xdc7654310), (0, 0xdc7653410), (0, 0xdc7654310), (1, 0xfd4675310),
  (1, 0xdc7654301), (1, 0xdc7653410), (0, 0xdc7653410), (0, 0xdc7654310),
  (0, 0xdc7654310), (1, 0xdc7654310), (1, 0xdc7564301), (1, 0xdc7654310),
  (0, 0xdc7654310), (0, 0xdc7643510), (0, 0xdc7654310), (1, 0xdc7654310),
  (1, 0xdc7654301), (1, 0xdc6754230), (0, 0xdc7653410), (0, 0xdc7654310),
  (0, 0xdc7654310), (1, 0xdc7654310), (1, 0xdc7654301), (1, 0xdc7645310),
  (1, 0xcd7654310), (0, 0xdc7653410), (0, 0xdc7654310), (1, 0xcd6754230),
  (1, 0xdc7654031), (1, 0xdc7654310), (0, 0xdc7653410), (0, 0xdc7654310),
  (0, 0xdc7654310), (1, 0xdc7654310), (1, 0xdc7564301), (1, 0xdc7654310),
  (0, 0xdc6574230), (1, 0xdc7654310), (0, 0xcd6574310), (1, 0xdc7654310),
  (1, 0xdc7654301), (1, 0xdc7654310), (0, 0xdc6573410), (0, 0xdc7654310),
  (0, 0xdc6574310), (1, 0xfc7654310), (1, 0xfc7654301), (1, 0xdc7654310),
  (0, 0xd7c654310), (0, 0xdc6573410), (1, 0xdc7654310), (1, 0xdc7654310),
  (2, 0xdc7654310), (2, 0xdc7654310), (0, 0xdc7653410), (0, 0xdc7654310),
  (0, 0xdc7651430), (1, 0xdc7546310), (1, 0xdc7654301), (1, 0xdc7654310),
  (0, 0xd7c654310), (0, 0xdc7653410), (0, 0xdc7654310), (1, 0xdc7654310),
  (1, 0xdc7654301), (1, 0xbdc564310), (0, 0xdc7653410), (0, 0xdc7654310),
  (0, 0xd7c654310), (1, 0xdc7654310), (1, 0xdc7653401), (1, 0xdc7654310),
  (0, 0xdc7654310), (0, 0xdc7653410), (0, 0xdc7654310), (1, 0xdc7654310),
  (1, 0xdc7654301), (1, 0xfc7635410), (0, 0xdc7653410), (0, 0xdc7654310),
  (0, 0xdc7654310), (1, 0xfd4675310), (1, 0xdc7654301), (1, 0xdc7653410),
  (0, 0xdc7654310), (0, 0xdc7653410), (0, 0xdc7654310), (1, 0xdc7654310),
  (1, 0xdc7564301), (1, 0xdc7654310), (0, 0xdc6573410), (0, 0xdc7645310),
  (0, 0xdc7654310), (1, 0xdc7654310), (1, 0xdc7654301), (1, 0xdc6754230),
  (0, 0xdc7654310), (0, 0xdc7653410), (0, 0xdc7654310), (1, 0xdc7654310),
  (1, 0xdc7654301), (1, 0xdc7645310), (1, 0xcd7654310), (0, 0xcd7654230),
  (0, 0xdc7654310), (1, 0xcd6754230), (1, 0xdc7654031), (1, 0xdc7654310),
  (0, 0xdc7653410), (0, 0xdc7653410), (0, 0xcd7653410), (1, 0xdc7654310),
  (1, 0xdc7564301), (1, 0xdc7654310), (0, 0xdc7653410), (1, 0xdc7654310),
  (0, 0xdc7654310), (1, 0xdc7654310), (1, 0xdc7654301), (1, 0xdc7654310),
  (0, 0xdc7654310), (0, 0xdc7653410), (0, 0xdc7654310), (1, 0xfc7654310),
  (1, 0xfc7654301), (1, 0xdc7654310), (0, 0xdc7653410), (0, 0xdc7654310),
  (1, 0xdc7654310), (1, 0xdc7654310), (3, 0xcd7654310), (3, 0xcd7654310),
  (0, 0xdc7654310), (0, 0xdc7653410), (0, 0xdc7654310), (1, 0xdc7546310),
  (1, 0xdc7654301), (1, 0xdc7654310)]

private def finiteCheck (n : Fin 162) : Bool :=
  let (i, rows) := certificates.get n
  pivotCheck 9 (checkedMinor (n.val + 2) i rows)

private lemma check_base : ∀ i : Fin 4, baseCheck i = true := by decide +kernel

private def checkBlock (start count : ℕ) : Bool :=
  (List.range' start count).all (fun n => finiteCheck (Fin.ofNat 162 n))

-- The kernel checks consecutive lengths together, sharing the recurring transfer factors.
set_option maxHeartbeats 0 in
private lemma check_finite (n : Fin 162) : finiteCheck n = true := by
  have h₁ : checkBlock 0 27 = true := by decide +kernel
  have h₂ : checkBlock 27 27 = true := by decide +kernel
  have h₃ : checkBlock 54 27 = true := by decide +kernel
  have h₄ : checkBlock 81 27 = true := by decide +kernel
  have h₅ : checkBlock 108 27 = true := by decide +kernel
  have h₆ : checkBlock 135 27 = true := by decide +kernel
  have consume (start : ℕ) (h : checkBlock start 27 = true)
      (lo : start ≤ n.val) (hi : n.val < start + 27) : finiteCheck n = true := by
    have hmem : n.val ∈ List.range' start 27 := List.mem_range'_1.mpr ⟨lo, hi⟩
    have hc := List.all_eq_true.mp h n.val hmem
    have hn : Fin.ofNat 162 n.val = n := Fin.ext (Nat.mod_eq_of_lt n.isLt)
    simpa only [hn] using hc
  by_cases h : n.val < 81
  · by_cases h' : n.val < 27
    · exact consume 0 h₁ (by omega) (by omega)
    · by_cases h'' : n.val < 54
      · exact consume 27 h₂ (by omega) (by omega)
      · exact consume 54 h₃ (by omega) (by omega)
  · by_cases h' : n.val < 108
    · exact consume 81 h₄ (by omega) (by omega)
    · by_cases h'' : n.val < 135
      · exact consume 108 h₅ (by omega) (by omega)
      · exact consume 135 h₆ (by omega) (by omega)

private lemma reduce_power {M : Type*} [Monoid M] (t : M)
    (h : t ^ 164 = t ^ 8) (k : ℕ) : t ^ (8 + k) = t ^ (8 + k % 156) := by
  have hp (l : ℕ) : t ^ (8 + l + 156) = t ^ (8 + l) := by
    rw [show 8 + l + 156 = 164 + l by omega, pow_add, h, ← pow_add]
  have repeatPeriod (q l : ℕ) : t ^ (8 + l + 156 * q) = t ^ (8 + l) := by
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, Nat.add_assoc 8 l, hp, ← Nat.add_assoc, ih]
  conv_lhs => rw [← Nat.mod_add_div k 156, ← Nat.add_assoc]
  apply repeatPeriod

private def reduced (m : ℕ) : ℕ := if m < 8 then m else 8 + (m - 8) % 156

private lemma reduced_bounds (m : ℕ) (hm : 2 ≤ m) :
    2 ≤ reduced m ∧ reduced m < 164 := by
  have hq : (m - 8) % 156 < 156 := Nat.mod_lt _ (by decide)
  unfold reduced
  split <;> omega

private lemma residue_reduced
    (period : ∀ i d, T i d ^ 164 = T i d ^ 8) (i : Fin 4) (m : ℕ) :
    residueAugmented (firstEntry i) (variableEntries i) m =
    residueAugmented (firstEntry i) (variableEntries i) (reduced m) := by
  unfold reduced
  split
  · rfl
  · rename_i hm
    have h (d : Direction) : T i d ^ m = T i d ^ (8 + (m - 8) % 156) := by
      nth_rw 1 [show m = 8 + (m - 8) by omega]
      exact reduce_power _ (period _ _) _
    have he (p : Entries) (d : Direction) :
        dualContraction (firstEntry i) (variableEntries i) d m p =
        dualContraction (firstEntry i) (variableEntries i) d (8 + (m - 8) % 156) p := by
      unfold dualContraction contraction
      change (_ * T i d ^ m).trace = (_ * T i d ^ (8 + (m - 8) % 156)).trace
      rw [h d]
    apply Matrix.ext
    intro p k
    refine Fin.cases ?_ (fun d => ?_) k <;>
      simp only [residueAugmented, Fin.cases_zero, Fin.cases_succ, he]

/-- For every ring length `r + 4`, a chart point has a nonsingular nine-column minor of
the actual raw two-site density and its eight coordinate derivatives. Complex nonsingularity
implies real independence including the radial column. -/
private theorem rank_of_certificates
    (period : ∀ i d, T i d ^ 164 = T i d ^ 8)
    (certificate : ∀ n, finiteCheck n = true) (r : ℕ) :
    ∃ (a : ℂ) (x : Fin 4 → ℂ) (rows : Fin 9 → Entries),
      ((augmented r a x).submatrix rows id).det ≠ 0 := by
  let m := r + 2
  have bounds := reduced_bounds m (by omega)
  let n : Fin 162 := ⟨reduced m - 2, by omega⟩
  have hcheck := certificate n
  change pivotCheck 9 (checkedMinor (n.val + 2)
    (certificates.get n).1 (certificates.get n).2) = true at hcheck
  have hm : n.val + 2 = reduced m := by
    dsimp [n]
    omega
  rw [hm] at hcheck
  let w := certificates.get n
  let a := firstEntry w.1
  let x := variableEntries w.1
  let rows := rowsOf w.2
  let B : Matrix (Fin 9) (Fin 9) G := (gaussianAugmented a x m).submatrix rows id
  have hc : (B.map residue).det ≠ 0 := by
    have he : B.map residue = entries (checkedMinor (reduced m) w.1 w.2) := by
      rw [checkedMinor_correct _ _ _ (by omega)]
      change ((gaussianAugmented a x m).map residue).submatrix rows id = _
      rw [residue_augmented, residue_reduced period w.1 m]
    rw [he]
    apply pivotCheck_det
    have hs {R : Type} {k : ℕ} (Q : Stored R k) : store (entries Q) = Q := by
      apply Vector.ext
      intro j hj
      apply Vector.ext
      intro l hl
      change ((Vector.ofFn fun u => Vector.ofFn fun v => entries Q u v).get ⟨j,hj⟩).get ⟨l,hl⟩ =
        (Q.get ⟨j,hj⟩).get ⟨l,hl⟩
      rw [vectorGetOfFn, vectorGetOfFn]
      rfl
    rw [hs]
    exact hcheck
  have hB : B.det ≠ 0 := by
    intro hz
    apply hc
    change (RingHom.mapMatrix residue B).det = 0
    rw [← residue.map_det, hz, map_zero]
  have heq : B.map complex =
      (augmented r (complex a) (fun j => complex (x j))).submatrix rows id := by
    change ((gaussianAugmented a x (r + 2)).map complex).submatrix rows id = _
    rw [complex_augmented]
  refine ⟨complex a, fun j => complex (x j), rows, ?_⟩
  rw [← heq]
  change (RingHom.mapMatrix complex B).det ≠ 0
  rw [← complex.map_det]
  intro hz
  have hi : Function.Injective complex :=
    Zsqrtd.lift_injective (R := ℂ) ⟨Complex.I, by simp⟩ minus_one_not_square
  exact hB (hi (hz.trans complex.map_zero.symm))


/-- For every ring length `r + 4`, a chart point has a nonsingular nine-column minor of
the actual raw two-site density and its eight coordinate derivatives. Complex nonsingularity
implies real independence including the radial column. -/
theorem projective_rank_eight (r : ℕ) :
    ∃ (a : ℂ) (x : Fin 4 → ℂ) (rows : Fin 9 → Entries),
      ((augmented r a x).submatrix rows id).det ≠ 0 :=
  rank_of_certificates (period_from_base check_base) check_finite r

#print axioms projective_rank_eight

end D5.S3.Quantum.TensorNetworks.PeriodicMPSTwoSiteDifferential
