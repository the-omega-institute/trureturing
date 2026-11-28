/- GID: D5/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuTwoModeCliffordPluecker
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unit Plücker coordinates for complex two-mode rank-two projections and their physical CAR cut weights. -/

import D5.S3.Quantum.Information.Pauli.PauliMatrix
import D5.S3.Quantum.Semigroups.WuCubicThermalBasis
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Module

/-! The Clifford and Plücker certificate for the complex two-mode Wu 2+2 orbit.
The occupation order is 00, 01, 10, 11. The mode order is right, then left.
The degree-one letters are the parity-twisted Majoranas. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Kronecker

namespace D5.S3.Quantum.Semigroups.WuTwoModeCliffordPluecker

open WuCubicOperatorBridge (Mat Occupation dissipator)
open WuCubicThermalBasis (e)
open TwistedTwoModeOUComparison (modeJump)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (Pauli pauliMatrix)
open private jump_zero jump_one from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

abbrev Edge := Fin 15
abbrev Coordinates := Edge → ℝ

/-- Lexicographically ordered pairs, with vertex labels starting at zero. -/
def edge : Edge → Fin 6 × Fin 6 :=
  ![(0,1), (0,2), (0,3), (0,4), (0,5),
    (1,2), (1,3), (1,4), (1,5),
    (2,3), (2,4), (2,5), (3,4), (3,5), (4,5)]

private def edgeIndex (i j : Fin 6) : Edge :=
  ![![0, 0, 1, 2, 3, 4],
    ![0, 0, 5, 6, 7, 8],
    ![0, 0, 0, 9, 10, 11],
    ![0, 0, 0, 0, 12, 13],
    ![0, 0, 0, 0, 0, 14],
    ![0, 0, 0, 0, 0, 0]] i j

/-- Extend the fifteen increasing coordinates to an alternating array. -/
def alternating (p : Coordinates) (i j : Fin 6) : ℝ :=
  if i < j then p (edgeIndex i j) else if j < i then -p (edgeIndex j i) else 0

/-- The four remaining vertices, in increasing order. -/
def complement : Edge → Fin 4 → Fin 6 :=
  ![![2, 3, 4, 5], ![1, 3, 4, 5], ![1, 2, 4, 5], ![1, 2, 3, 5], ![1, 2, 3, 4],
    ![0, 3, 4, 5], ![0, 2, 4, 5], ![0, 2, 3, 5], ![0, 2, 3, 4],
    ![0, 1, 4, 5], ![0, 1, 3, 5], ![0, 1, 3, 4],
    ![0, 1, 2, 5], ![0, 1, 2, 4], ![0, 1, 2, 3]]

/-- The indexed relation uses the four vertices complementary to the indexed edge. -/
def pluecker (p : Coordinates) (k : Edge) : ℝ :=
  let q := complement k
  alternating p (q 0) (q 1) * alternating p (q 2) (q 3) -
    alternating p (q 0) (q 2) * alternating p (q 1) (q 3) +
    alternating p (q 0) (q 3) * alternating p (q 1) (q 2)

private def complementSign : Edge → ℝ :=
  ![-1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1]

def sqNorm (p : Coordinates) : ℝ :=
  ∑ k : Edge, p k ^ 2

private def occupationIndex (i : Occupation) : Fin 4 :=
  ![![0, 1], ![2, 3]] i.1 i.2

private def occupancyMatrix (A : Matrix (Fin 4) (Fin 4) ℂ) : Mat :=
  fun i j => A (occupationIndex i) (occupationIndex j)

/-- The audit's jumps `Z ⊗ e, e ⊗ I`. The sign on the right jump is a phase
relative to the repository convention. -/
def jump (j : Fin 2) : Mat :=
  ![-modeJump 1, modeJump 0] j

theorem jump_right : jump 0 = pauliMatrix Pauli.Z ⊗ₖ e := by
  change -modeJump 1 = pauliMatrix Pauli.Z ⊗ₖ e
  rw [jump_one]
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitZ, e,
      Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Matrix.neg_apply]

theorem jump_left : jump 1 = e ⊗ₖ pauliMatrix Pauli.I := by
  change modeJump 0 = e ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  exact jump_zero

/-- The raw jump Majoranas, two per mode. -/
def rawMajorana (a : Fin 4) : Mat :=
  ![jump 0 + (jump 0)ᴴ, Complex.I • (jump 0 - (jump 0)ᴴ),
    jump 1 + (jump 1)ᴴ, Complex.I • (jump 1 - (jump 1)ᴴ)] a

def gamma : Mat :=
  rawMajorana 0 * rawMajorana 1 * rawMajorana 2 * rawMajorana 3

/-- The five Clifford generators, in the order of the audit. -/
def g (a : Fin 5) : Mat :=
  ![Complex.I • (gamma * rawMajorana 0), Complex.I • (gamma * rawMajorana 1),
    Complex.I • (gamma * rawMajorana 2), Complex.I • (gamma * rawMajorana 3), gamma] a

/-- The fifteen Hermitian letters. Pairs incident to vertex 5 use a single generator. -/
def B (k : Edge) : Mat :=
  let (i, j) := edge k
  let first : Fin 5 := ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
  let second : Fin 5 := ⟨j.val % 5, Nat.mod_lt _ (by decide)⟩
  if j = 5 then g first else Complex.I • (g first * g second)

private def rawEntries : Fin 4 → Mat :=
  ![occupancyMatrix !![0, 1, 0, 0;
      1, 0, 0, 0;
      0, 0, 0, -1;
      0, 0, -1, 0],
    occupancyMatrix !![0, Complex.I, 0, 0;
      -Complex.I, 0, 0, 0;
      0, 0, 0, -Complex.I;
      0, 0, Complex.I, 0],
    occupancyMatrix !![0, 0, 1, 0;
      0, 0, 0, 1;
      1, 0, 0, 0;
      0, 1, 0, 0],
    occupancyMatrix !![0, 0, Complex.I, 0;
      0, 0, 0, Complex.I;
      -Complex.I, 0, 0, 0;
      0, -Complex.I, 0, 0]]

private theorem rawMajorana_eq_entries (k : Fin 4) :
    rawMajorana k = rawEntries k := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases k <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [rawMajorana, rawEntries, jump_right, jump_left, pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitZ, e, occupancyMatrix, occupationIndex,
      Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, Complex.star_def,
      Complex.mul_re, Complex.mul_im]

set_option maxHeartbeats 1500000 in
-- The product of four Majoranas expands over the physical occupation indices.
private theorem gamma_eq_entries :
    gamma = occupancyMatrix !![-1, 0, 0, 0;
      0, 1, 0, 0;
      0, 0, 1, 0;
      0, 0, 0, -1] := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [gamma, rawMajorana_eq_entries, rawEntries, occupancyMatrix, occupationIndex,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]

private def gEntries : Fin 5 → Mat :=
  ![occupancyMatrix !![0, -Complex.I, 0, 0;
      Complex.I, 0, 0, 0;
      0, 0, 0, -Complex.I;
      0, 0, Complex.I, 0],
    occupancyMatrix !![0, 1, 0, 0;
      1, 0, 0, 0;
      0, 0, 0, 1;
      0, 0, 1, 0],
    occupancyMatrix !![0, 0, -Complex.I, 0;
      0, 0, 0, Complex.I;
      Complex.I, 0, 0, 0;
      0, -Complex.I, 0, 0],
    occupancyMatrix !![0, 0, 1, 0;
      0, 0, 0, -1;
      1, 0, 0, 0;
      0, -1, 0, 0],
    occupancyMatrix !![-1, 0, 0, 0;
      0, 1, 0, 0;
      0, 0, 1, 0;
      0, 0, 0, -1]]

private theorem g_eq_entries (k : Fin 5) : g k = gEntries k := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases k <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [g, gEntries, gamma_eq_entries, rawMajorana_eq_entries, rawEntries, occupancyMatrix,
      occupationIndex, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]

set_option maxHeartbeats 3000000 in
-- Checking each generator pair expands both products entry by entry.
theorem clifford (i j : Fin 5) :
    g i * g j + g j * g i = if i = j then (2 : ℂ) • (1 : Mat) else 0 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases i <;> fin_cases j <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [g_eq_entries, gEntries, occupancyMatrix, occupationIndex, Matrix.mul_apply,
      Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]

set_option maxHeartbeats 2000000 in
-- The five-generator product expands over the physical occupation indices.
theorem clifford_volume : g 0 * g 1 * g 2 * g 3 * g 4 = 1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [g_eq_entries, gEntries, occupancyMatrix, occupationIndex, Matrix.mul_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]

set_option maxHeartbeats 3000000 in
-- Checking both products for each Majorana pair requires entrywise expansion.
theorem twisted_mul (i j : Fin 4) :
    g (Fin.castLE (by decide) i) * g (Fin.castLE (by decide) j) =
      rawMajorana i * rawMajorana j := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases i <;> fin_cases j <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [g_eq_entries, gEntries, rawMajorana_eq_entries, rawEntries, occupancyMatrix,
      occupationIndex, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]

set_option maxHeartbeats 4000000 in
-- The conjugation check expands a triple matrix product for each pair of letters.
theorem raw_conjugation (i : Fin 4) (j : Fin 5) :
    rawMajorana i * g j * rawMajorana i =
      if i.val = j.val ∨ j = 4 then -g j else g j := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases i <;> fin_cases j <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [g_eq_entries, gEntries, rawMajorana_eq_entries, rawEntries, occupancyMatrix,
      occupationIndex, Matrix.of_apply, Matrix.mul_apply, Matrix.neg_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]

/-- Entry form of the Clifford expansion, with scalar coefficient `s`. -/
def matrixOf (s : ℝ) (p : Coordinates) : Mat :=
  occupancyMatrix !![⟨s + p 0 + p 9 - p 14, 0⟩,
      ⟨p 3 + p 8, -p 4 + p 7⟩,
      ⟨p 10 + p 13, -p 11 + p 12⟩,
      ⟨-p 2 - p 5, p 1 - p 6⟩;
    ⟨p 3 + p 8, p 4 - p 7⟩,
      ⟨s - p 0 + p 9 + p 14, 0⟩,
      ⟨-p 2 + p 5, p 1 + p 6⟩,
      ⟨p 10 - p 13, p 11 + p 12⟩;
    ⟨p 10 + p 13, p 11 - p 12⟩,
      ⟨-p 2 + p 5, -p 1 - p 6⟩,
      ⟨s + p 0 - p 9 + p 14, 0⟩,
      ⟨-p 3 + p 8, -p 4 - p 7⟩;
    ⟨-p 2 - p 5, -p 1 + p 6⟩,
      ⟨p 10 - p 13, -p 11 - p 12⟩,
      ⟨-p 3 + p 8, p 4 + p 7⟩,
      ⟨s - p 0 - p 9 - p 14, 0⟩]

/-- Expansion in the fifteen traceless Clifford letters. -/
def expand (p : Coordinates) : Mat := matrixOf 0 p

private def unitCoordinate (k : Edge) : Coordinates := fun l => if k = l then 1 else 0

set_option maxHeartbeats 3000000 in
-- The entrywise calculation checks all fifteen letters in the physical basis.
private theorem B_eq_matrixOf (k : Edge) : B k = matrixOf 0 (unitCoordinate k) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases k <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [B, edge, g_eq_entries, gEntries, matrixOf, unitCoordinate,
      occupancyMatrix, occupationIndex, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]

set_option maxHeartbeats 2000000 in
-- Expanding the fifteen-letter sum at each physical matrix entry needs extra heartbeats.
theorem expand_eq_sum (p : Coordinates) : expand p = ∑ k : Edge, (p k : ℂ) • B k := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [expand, matrixOf, B_eq_matrixOf, unitCoordinate, occupancyMatrix, occupationIndex,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum] <;> ring

theorem matrixOf_hermitian (s : ℝ) (p : Coordinates) : (matrixOf s p).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    simp [matrixOf, occupancyMatrix, occupationIndex, Complex.star_def] <;> ring

theorem trace_matrixOf (s : ℝ) (p : Coordinates) :
    (matrixOf s p).trace = ((4 * s : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [matrixOf, occupancyMatrix, occupationIndex, Matrix.trace, Matrix.diag,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.add_re, Complex.add_im] <;> ring

/-- Invert the four diagonal and six upper-triangular entries of the expansion. -/
def coordinates (A : Mat) : Coordinates :=
  let a := A (0,0) (0,0)
  let b := A (0,1) (0,1)
  let c := A (1,0) (1,0)
  let d := A (1,1) (1,1)
  let x := A (0,0) (0,1)
  let y := A (0,0) (1,0)
  let z := A (0,0) (1,1)
  let w := A (0,1) (1,0)
  let v := A (0,1) (1,1)
  let t := A (1,0) (1,1)
  ![(a.re - b.re + c.re - d.re) / 4,
    (z.im + w.im) / 2, -(z.re + w.re) / 2,
    (x.re - t.re) / 2, -(x.im + t.im) / 2,
    (w.re - z.re) / 2, (w.im - z.im) / 2,
    (x.im - t.im) / 2, (x.re + t.re) / 2,
    (a.re + b.re - c.re - d.re) / 4,
    (y.re + v.re) / 2, (v.im - y.im) / 2,
    (y.im + v.im) / 2, (y.re - v.re) / 2,
    (-a.re + b.re + c.re - d.re) / 4]

theorem coordinates_matrixOf (s : ℝ) (p : Coordinates) :
    coordinates (matrixOf s p) = p := by
  funext k
  fin_cases k <;> simp [coordinates, matrixOf, occupancyMatrix, occupationIndex] <;> ring

theorem matrixOf_coordinates {A : Mat} (hA : A.IsHermitian) :
    matrixOf (A.trace.re / 4) (coordinates A) = A := by
  have hre (i j : Occupation) : (A j i).re = (A i j).re := by
    simpa [Complex.star_def] using congrArg Complex.re (hA.apply i j)
  have him (i j : Occupation) : (A j i).im = -(A i j).im := by
    have h : -(A j i).im = (A i j).im := by
      simpa [Complex.star_def] using congrArg Complex.im (hA.apply i j)
    linarith only [h]
  have hd (i : Occupation) : (A i i).im = 0 := by linarith only [him i i]
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    simp [matrixOf, coordinates, occupancyMatrix, occupationIndex, Matrix.trace, Matrix.diag,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.add_re, hd,
      hre (0,0) (0,1), hre (0,0) (1,0), hre (0,0) (1,1),
      hre (0,1) (1,0), hre (0,1) (1,1), hre (1,0) (1,1),
      him (0,0) (0,1), him (0,0) (1,0), him (0,0) (1,1),
      him (0,1) (1,0), him (0,1) (1,1), him (1,0) (1,1)] <;> ring

theorem expand_coordinates {A : Mat} (hA : A.IsHermitian) (ht : A.trace = 0) :
    expand (coordinates A) = A := by
  simpa [expand, ht] using matrixOf_coordinates hA

set_option maxHeartbeats 3000000 in
-- The trace expands a physical matrix product for each of the fifteen letters.
theorem trace_mul_B (s : ℝ) (p : Coordinates) (k : Edge) :
    (matrixOf s p * B k).trace = ((4 * p k : ℝ) : ℂ) := by
  fin_cases k <;> apply Complex.ext <;>
    norm_num [B_eq_matrixOf, matrixOf, unitCoordinate, occupancyMatrix, occupationIndex,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

theorem B_hermitian (k : Edge) : (B k).IsHermitian := by
  rw [B_eq_matrixOf]
  exact matrixOf_hermitian _ _

theorem trace_B (k : Edge) : (B k).trace = 0 := by
  rw [B_eq_matrixOf, trace_matrixOf]
  norm_num

theorem trace_B_mul_B (k l : Edge) :
    (B k * B l).trace = if k = l then 4 else 0 := by
  rw [B_eq_matrixOf k, trace_mul_B]
  by_cases h : k = l <;> simp [unitCoordinate, h]

private theorem matrixOf_one :
    matrixOf 1 (0 : Coordinates) = 1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [matrixOf, occupancyMatrix, occupationIndex, Matrix.one_apply]

set_option maxHeartbeats 4000000 in
-- The entrywise square expands products of the fifteen coordinate terms.
/-- The scalar part of the square is the squared norm. Each remaining coefficient
is twice the signed Plücker relation on the complementary vertices. -/
theorem expand_square (p : Coordinates) :
    expand p * expand p =
      matrixOf (sqNorm p) (fun k => 2 * complementSign k * pluecker p k) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [expand, matrixOf, occupancyMatrix, occupationIndex, sqNorm, pluecker, complement,
      complementSign, alternating, edgeIndex, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im] <;> ring

private theorem complementSign_ne_zero (k : Edge) : complementSign k ≠ 0 := by
  fin_cases k <;> norm_num [complementSign]

theorem expand_square_eq_one_iff (p : Coordinates) :
    expand p * expand p = 1 ↔ sqNorm p = 1 ∧ ∀ k, pluecker p k = 0 := by
  rw [expand_square, ← matrixOf_one]
  constructor
  · intro h
    have hs := congrArg (fun A : Mat => A.trace.re) h
    have hp := congrArg coordinates h
    simp only [trace_matrixOf, Complex.ofReal_re] at hs
    simp only [coordinates_matrixOf] at hp
    refine ⟨by linarith only [hs], fun k => ?_⟩
    have hk : 2 * complementSign k * pluecker p k = 0 := congrFun hp k
    exact (mul_eq_zero.mp hk).resolve_left (mul_ne_zero (by norm_num) (complementSign_ne_zero k))
  · rintro ⟨hs, hp⟩
    have hzero : (fun k => 2 * complementSign k * pluecker p k) = (0 : Coordinates) := by
      funext k
      simp only [hp, mul_zero, Pi.zero_apply]
    rw [hs, hzero]

/-- The trace and rank of an idempotent agree via the existing projection trace theorem. -/
theorem trace_eq_rank_of_idempotent {P : Mat} (hP : P * P = P) :
    P.trace = (P.rank : ℂ) := by
  have h : IsIdempotentElem P.toLin' := by
    change P.toLin' * P.toLin' = P.toLin'
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have ht := (LinearMap.IsIdempotentElem.isProj_range P.toLin' h).trace
  rw [Matrix.trace_toLin'_eq] at ht
  change P.trace = (P.rank : ℂ) at ht
  exact ht

def involution (P : Mat) : Mat := (2 : ℂ) • P - 1

private theorem involution_hermitian {P : Mat} (hP : P.IsHermitian) :
    (involution P).IsHermitian := by
  change (involution P)ᴴ = involution P
  simp [involution, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP.eq]

private theorem involution_square {P : Mat} (hP : P * P = P) :
    involution P * involution P = 1 := by
  simp only [involution, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, hP,
    mul_one, one_mul, smul_smul]
  module

theorem rank_two_projection_certificate {P : Mat}
    (hHerm : P.IsHermitian) (hP : P * P = P) (hRank : P.rank = 2) :
    let p := coordinates (involution P)
    involution P = (∑ k : Edge, (p k : ℂ) • B k) ∧
      sqNorm p = 1 ∧ ∀ k, pluecker p k = 0 := by
  dsimp only
  have htrace : P.trace = 2 := by rw [trace_eq_rank_of_idempotent hP, hRank]; norm_num
  have ht : (involution P).trace = 0 := by
    norm_num [involution, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, htrace]
  have hexpand := expand_coordinates (involution_hermitian hHerm) ht
  refine ⟨hexpand.symm.trans (expand_eq_sum _), (expand_square_eq_one_iff _).mp ?_⟩
  rw [hexpand]
  exact involution_square hP

/-- Every unit solution of the Plücker relations yields a rank-two orthogonal projection. -/
theorem projection_of_coordinates (p : Coordinates) (hn : sqNorm p = 1)
    (hp : ∀ k, pluecker p k = 0) :
    ∃ P : Mat, P.IsHermitian ∧ P * P = P ∧ P.rank = 2 ∧ involution P = expand p := by
  let P := (1 / 2 : ℂ) • (expand p + 1)
  have hK := (expand_square_eq_one_iff p).mpr ⟨hn, hp⟩
  have hHerm := (matrixOf_hermitian 0 p).eq
  have hHerm' : (expand p)ᴴ = expand p := hHerm
  have hP : P * P = P := by
    simp only [P, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hK,
      mul_one, one_mul, smul_smul]
    module
  have ht : (expand p).trace = 0 := by norm_num [expand, trace_matrixOf]
  have htr : P.trace = 2 := by
    norm_num [P, Matrix.trace_add, Matrix.trace_one, Matrix.trace_smul, ht]
  refine ⟨P, ?_, hP, ?_, ?_⟩
  · change Pᴴ = P
    simp [P, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hHerm']
  · have h := (trace_eq_rank_of_idempotent hP).symm.trans htr
    exact_mod_cast h
  · simp only [involution, P, smul_smul]
    module

/-- The signed occupation matrix for a physical lowering jump. -/
def occupation (j : Fin 2) : Mat :=
  1 - (2 : ℂ) • ((jump j)ᴴ * jump j)

theorem B_occupation (j : Fin 2) : B (![0, 9] j) = occupation j := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases j <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [B_eq_matrixOf, matrixOf, unitCoordinate, occupancyMatrix, occupationIndex,
      occupation, jump_right, jump_left, pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitZ,
      e, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Fintype.sum_prod_type, Fin.sum_univ_two, Complex.star_def, Complex.mul_re, Complex.mul_im]

/-- The two signed occupation traces recover the 12 and 34 coordinates. -/
theorem occupation_trace (p : Coordinates) (j : Fin 2) :
    ((expand p * occupation j).trace.re / 4) = p (![0, 9] j) := by
  rw [← B_occupation j, expand, trace_mul_B, Complex.ofReal_re]
  ring

/-- The local tracial Wu generator in the right-then-left mode order. -/
def tracial (j : Fin 2) (X : Mat) : Mat :=
  dissipator (jump j) X + dissipator (jump j)ᴴ X

theorem tracial_eq_repository (j : Fin 2) (X : Mat) :
    tracial j X = dissipator (modeJump (1 - j)) X + dissipator (modeJump (1 - j))ᴴ X := by
  have phase (J : Mat) : dissipator (-J) X = dissipator J X := by simp [dissipator]
  fin_cases j <;> norm_num [tracial, jump, Matrix.conjTranspose_neg, phase]

/-- Local tracial degrees in the lexicographic pair order of `edge`. -/
def modeDegree (j : Fin 2) (k : Edge) : ℕ :=
  ![![2, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 0, 2, 0, 2],
    ![0, 1, 1, 2, 0, 1, 1, 2, 0, 2, 1, 1, 1, 1, 2]] j k

set_option maxHeartbeats 5000000 in
-- Expanding both jump dissipators over the four physical indices needs extra heartbeats.
theorem tracial_expand (j : Fin 2) (p : Coordinates) :
    tracial j (expand p) = expand (fun k => (modeDegree j k : ℝ) * p k) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases j <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [tracial, dissipator, modeDegree, jump_right, jump_left, pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitZ, e, expand, matrixOf, occupancyMatrix,
      occupationIndex, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply,
      Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.conjTranspose_apply, smul_eq_mul, Fintype.sum_prod_type, Fin.sum_univ_two,
      Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im] <;> ring

theorem trace_expand_mul_expand (p q : Coordinates) :
    (expand p * expand q).trace.re / 4 = ∑ k : Edge, p k * q k := by
  conv_lhs => rw [expand_eq_sum q]
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    expand, trace_mul_B, smul_eq_mul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The exact diagonal quadratic form used in the orientation cost. -/
theorem tracial_quadratic (j : Fin 2) (p : Coordinates) :
    (expand p * tracial j (expand p)).trace.re / 4 =
      ∑ k : Edge, (modeDegree j k : ℝ) * p k ^ 2 := by
  rw [tracial_expand, trace_expand_mul_expand]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem jump_car (j : Fin 2) :
    jump j * (jump j)ᴴ + (jump j)ᴴ * jump j = 1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases j <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    apply Complex.ext <;>
    norm_num [jump_right, jump_left, pauliMatrix, D5.S3.Quantum.FiniteDimensional.qubitZ,
      e, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]

private theorem tracial_eq_sub (j : Fin 2) (X : Mat) :
    tracial j X = X - (jump j)ᴴ * X * jump j - jump j * X * (jump j)ᴴ := by
  let J := jump j
  have hCAR : Jᴴ * J + J * Jᴴ = 1 := (add_comm _ _).trans (jump_car j)
  have hA :
      (Jᴴ * J * X + X * (Jᴴ * J)) + (J * Jᴴ * X + X * (J * Jᴴ)) = X + X := by
    calc
      _ = (Jᴴ * J + J * Jᴴ) * X + X * (Jᴴ * J + J * Jᴴ) := by
        simp only [add_mul, mul_add]
        abel
      _ = _ := by rw [hCAR, one_mul, mul_one]
  unfold tracial dissipator
  rw [Matrix.conjTranspose_conjTranspose]
  change (1 / 2 : ℂ) • (Jᴴ * J * X + X * (Jᴴ * J)) - Jᴴ * X * J +
      ((1 / 2 : ℂ) • (J * Jᴴ * X + X * (J * Jᴴ)) - J * X * Jᴴ) = _
  calc
    _ = (1 / 2 : ℂ) • ((Jᴴ * J * X + X * (Jᴴ * J)) +
        (J * Jᴴ * X + X * (J * Jᴴ))) - Jᴴ * X * J - J * X * Jᴴ := by
      simp only [smul_add]
      abel
    _ = _ := by
      rw [hA]
      module

/-- The within-block jump weight of a rank-two projection. -/
def within (P : Mat) (j : Fin 2) : ℂ := (P * jump j * P * (jump j)ᴴ).trace

theorem trace_involution_tracial {P : Mat} (hP : P * P = P) (hRank : P.rank = 2)
    (j : Fin 2) :
    (involution P * tracial j (involution P)).trace = 8 * (1 - within P j) := by
  let J := jump j
  let K := involution P
  have hCAR : J * Jᴴ + Jᴴ * J = 1 := jump_car j
  have h₄ : (1 : Mat).trace = 4 := by norm_num [Matrix.trace_one]
  have h₂ : P.trace = 2 := by rw [trace_eq_rank_of_idempotent hP, hRank]; norm_num
  have hJ : (J * Jᴴ).trace = 2 := by
    have h := congrArg (fun A : Mat => A.trace) hCAR
    change (J * Jᴴ + Jᴴ * J).trace = (1 : Mat).trace at h
    rw [Matrix.trace_add, Matrix.trace_mul_comm Jᴴ J, h₄] at h
    linear_combination (1 / 2 : ℂ) * h
  have hPJ : (P * J * Jᴴ).trace + (J * P * Jᴴ).trace = 2 := by
    have hcycle : (J * P * Jᴴ).trace = (P * (Jᴴ * J)).trace := by
      rw [Matrix.mul_assoc J P Jᴴ, Matrix.trace_mul_comm J (P * Jᴴ), Matrix.mul_assoc]
    rw [hcycle, Matrix.mul_assoc P J Jᴴ, ← Matrix.trace_add, ← Matrix.mul_add,
      hCAR, Matrix.mul_one, h₂]
  have hKJ : (K * J * K * Jᴴ).trace = 4 * within P j - 2 := by
    have hexpand :
        (K * J * K * Jᴴ).trace =
          4 * within P j - 2 * (P * J * Jᴴ).trace -
            2 * (J * P * Jᴴ).trace + (J * Jᴴ).trace := by
      simp only [K, involution, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        one_mul, mul_one, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
      change _ = 4 * (P * J * P * Jᴴ).trace - 2 * (P * J * Jᴴ).trace -
        2 * (J * P * Jᴴ).trace + (J * Jᴴ).trace
      ring
    rw [hexpand, hJ]
    linear_combination -2 * hPJ
  have hswap : (K * Jᴴ * K * J).trace = (K * J * K * Jᴴ).trace := by
    calc
      _ = ((K * Jᴴ) * (K * J)).trace := by rw [← Matrix.mul_assoc]
      _ = ((K * J) * (K * Jᴴ)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by rw [← Matrix.mul_assoc]
  have hKK : K * K = 1 := involution_square hP
  have hL : tracial j K = K - Jᴴ * K * J - J * K * Jᴴ := tracial_eq_sub j K
  change (K * tracial j K).trace = _
  rw [hL]
  simp only [mul_sub, Matrix.trace_sub, ← Matrix.mul_assoc]
  rw [hKK, h₄, hswap, hKJ]
  ring

theorem within_quadratic {P : Mat} (hHerm : P.IsHermitian) (hP : P * P = P)
    (hRank : P.rank = 2) (j : Fin 2) :
    let p := coordinates (involution P)
    2 * (1 - (within P j).re) = ∑ k : Edge, (modeDegree j k : ℝ) * p k ^ 2 := by
  let p := coordinates (involution P)
  change 2 * (1 - (within P j).re) = ∑ k : Edge, (modeDegree j k : ℝ) * p k ^ 2
  have hcert : involution P = expand p :=
    (rank_two_projection_certificate hHerm hP hRank).1.trans (expand_eq_sum p).symm
  have htrace := congrArg Complex.re (trace_involution_tracial hP hRank j)
  rw [hcert] at htrace
  norm_num [Complex.mul_re, Complex.sub_re] at htrace
  rw [← tracial_quadratic, htrace]
  ring

private theorem alternating_edge (p : Coordinates) (k : Edge) :
    alternating p (edge k).1 (edge k).2 = p k := by
  fin_cases k <;> norm_num [alternating, edge, edgeIndex]

private theorem edge_of_index :
    ∀ i j : Fin 6, i < j → edge (edgeIndex i j) = (i,j) := by decide

set_option maxHeartbeats 1000000 in
-- The finite case split checks that every increasing quadruple is in the complement table.
private theorem complement_covers :
    ∀ a b c d : Fin 6, a < b → b < c → c < d →
      ∃ k : Edge, complement k 0 = a ∧ complement k 1 = b ∧
        complement k 2 = c ∧ complement k 3 = d := by
  intro a b c d hab hbc hcd
  fin_cases a <;> fin_cases b <;> norm_num at hab
  all_goals fin_cases c <;> norm_num at hbc
  all_goals fin_cases d <;> norm_num at hcd
  all_goals
    simp only [Fin.exists_fin_succ, Fin.exists_fin_zero]
    decide

private theorem alternating_diag (p : Coordinates) (i : Fin 6) :
    alternating p i i = 0 := by simp [alternating]

private theorem alternating_skew (p : Coordinates) (i j : Fin 6) :
    alternating p j i = -alternating p i j := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [alternating, hij, not_lt_of_gt hij]
  · simp [alternating]
  · simp [alternating, hji, not_lt_of_gt hji]

private def plueckerExpr (q : Fin 6 → Fin 6 → ℝ) (a b c d : Fin 6) : ℝ :=
  q a b * q c d - q a c * q b d + q a d * q b c

private theorem plueckerExpr_zero (p : Coordinates) (hp : ∀ k, pluecker p k = 0)
    (a b c d : Fin 6) : plueckerExpr (alternating p) a b c d = 0 := by
  let F := plueckerExpr (alternating p)
  have swap₁ (a b c d : Fin 6) : F b a c d = -F a b c d := by
    simp only [F, plueckerExpr, alternating_skew p a b]
    ring
  have swap₂ (a b c d : Fin 6) : F a c b d = -F a b c d := by
    simp only [F, plueckerExpr, alternating_skew p b c]
    ring
  have swap₃ (a b c d : Fin 6) : F a b d c = -F a b c d := by
    simp only [F, plueckerExpr, alternating_skew p c d]
    ring
  have swap₁₃ (a b c d : Fin 6) : F c b a d = -F a b c d := by
    simp only [F, plueckerExpr, alternating_skew p a b, alternating_skew p b c,
      alternating_skew p a c]
    ring
  have swap₂₄ (a b c d : Fin 6) : F a d c b = -F a b c d := by
    simp only [F, plueckerExpr, alternating_skew p b c, alternating_skew p b d,
      alternating_skew p c d]
    ring
  have ordered (a b c d : Fin 6) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
      F a b c d = 0 := by
    rcases eq_or_lt_of_le hab with rfl | hab
    · simp [F, plueckerExpr, alternating_diag] <;> ring
    rcases eq_or_lt_of_le hbc with rfl | hbc
    · simp [F, plueckerExpr, alternating_diag]
    rcases eq_or_lt_of_le hcd with rfl | hcd
    · simp [F, plueckerExpr, alternating_diag] <;> ring
    obtain ⟨k, rfl, rfl, rfl, rfl⟩ := complement_covers a b c d hab hbc hcd
    exact hp k
  have cmp₁ (a b c d : Fin 6) : F (min a b) (max a b) c d = 0 ↔ F a b c d = 0 := by
    rcases le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, swap₁, neg_eq_zero]
  have cmp₂ (a b c d : Fin 6) : F a (min b c) (max b c) d = 0 ↔ F a b c d = 0 := by
    rcases le_total b c with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, swap₂, neg_eq_zero]
  have cmp₃ (a b c d : Fin 6) : F a b (min c d) (max c d) = 0 ↔ F a b c d = 0 := by
    rcases le_total c d with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, swap₃, neg_eq_zero]
  have cmp₁₃ (a b c d : Fin 6) : F (min a c) b (max a c) d = 0 ↔ F a b c d = 0 := by
    rcases le_total a c with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, swap₁₃, neg_eq_zero]
  have cmp₂₄ (a b c d : Fin 6) : F a (min b d) c (max b d) = 0 ↔ F a b c d = 0 := by
    rcases le_total b d with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, swap₂₄, neg_eq_zero]
  -- Compare (1,2), (3,4), (1,3), (2,4), (2,3).
  let a₁ := min a b
  let b₁ := max a b
  let c₁ := min c d
  let d₁ := max c d
  let a₂ := min a₁ c₁
  let b₂ := min b₁ d₁
  let c₂ := max a₁ c₁
  let d₂ := max b₁ d₁
  apply (cmp₁ a b c d).mp
  apply (cmp₃ a₁ b₁ c d).mp
  apply (cmp₁₃ a₁ b₁ c₁ d₁).mp
  apply (cmp₂₄ a₂ b₁ c₂ d₁).mp
  apply (cmp₂ a₂ b₂ c₂ d₂).mp
  exact ordered a₂ (min b₂ c₂) (max b₂ c₂) d₂
    (le_min (min_le_min min_le_max min_le_max) min_le_max)
    min_le_max
    (max_le min_le_max (max_le_max min_le_max min_le_max))

/-- The fifteen signed two-by-two minors of a real pair of vectors. -/
def wedge (u v : Fin 6 → ℝ) : Coordinates :=
  fun k => u (edge k).1 * v (edge k).2 - u (edge k).2 * v (edge k).1

private theorem alternating_wedge (u v : Fin 6 → ℝ) (i j : Fin 6) :
    alternating (wedge u v) i j = u i * v j - u j * v i := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [alternating, hij, wedge, edge_of_index i j hij]
  · simp [alternating]
  · simp [alternating, hji, not_lt_of_gt hji, wedge, edge_of_index j i hji] <;> ring

theorem pluecker_wedge (u v : Fin 6 → ℝ) (k : Edge) : pluecker (wedge u v) k = 0 := by
  simp only [pluecker, alternating_wedge]
  ring

/-- A nonzero coordinate supplies a pivot for all fifteen minors. -/
theorem exists_wedge (p : Coordinates) (hn : sqNorm p ≠ 0)
    (hp : ∀ k, pluecker p k = 0) : ∃ u v : Fin 6 → ℝ, wedge u v = p := by
  obtain ⟨k, hk⟩ : ∃ k, p k ≠ 0 := by
    by_contra! h
    exact hn (by simp [sqNorm, h])
  let a := (edge k).1
  let b := (edge k).2
  refine ⟨alternating p a, fun i => alternating p b i / p k, ?_⟩
  funext l
  have h := plueckerExpr_zero p hp a b (edge l).1 (edge l).2
  change alternating p (edge k).1 (edge k).2 * alternating p (edge l).1 (edge l).2 -
    alternating p a (edge l).1 * alternating p b (edge l).2 +
    alternating p a (edge l).2 * alternating p b (edge l).1 = 0 at h
  rw [alternating_edge, alternating_edge] at h
  dsimp only [wedge]
  simp only [← mul_div_assoc, ← sub_div]
  apply (div_eq_iff hk).2
  linear_combination -h

/-- Euclidean inner product of the six real coordinates. -/
def inner (u v : Fin 6 → ℝ) : ℝ := ∑ i : Fin 6, u i * v i

theorem sqNorm_wedge (u v : Fin 6 → ℝ) :
    sqNorm (wedge u v) = inner u u * inner v v - inner u v ^ 2 := by
  simp [sqNorm, wedge, edge, inner, Fin.sum_univ_succ] <;> ring

/-- Unit solutions of the relations are exactly the oriented orthonormal plane coordinates. -/
theorem unit_pluecker_iff (p : Coordinates) :
    (sqNorm p = 1 ∧ ∀ k, pluecker p k = 0) ↔
      ∃ u v : Fin 6 → ℝ, inner u u = 1 ∧ inner v v = 1 ∧ inner u v = 0 ∧ wedge u v = p := by
  constructor
  · rintro ⟨hn, hp⟩
    obtain ⟨u, v, hw⟩ := exists_wedge p (by rw [hn]; norm_num) hp
    have hn' : sqNorm (wedge u v) = 1 := by simpa only [hw] using hn
    have hu : 0 < inner u u := by
      apply lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (u i))
      intro hz
      have hzero (i : Fin 6) : u i = 0 :=
        (Finset.sum_mul_self_eq_zero_iff Finset.univ u).mp hz.symm i (Finset.mem_univ i)
      simp [sqNorm, wedge, hzero] at hn'
    let r := Real.sqrt (inner u u)
    have hr : 0 < r := Real.sqrt_pos.2 hu
    have hr2 : r ^ 2 = inner u u := Real.sq_sqrt hu.le
    let x : Fin 6 → ℝ := fun i => u i / r
    let c := inner x v
    let y : Fin 6 → ℝ := fun i => r * (v i - c * x i)
    have hxx : inner x x = 1 := by
      calc
        inner x x = (∑ i : Fin 6, u i * u i) * (r ^ 2)⁻¹ := by
          unfold inner
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [x]
          rw [div_mul_div_comm, pow_two, div_eq_mul_inv]
        _ = 1 := by rw [hr2]; exact mul_inv_cancel₀ hu.ne'
    have hxy : inner x y = 0 := by
      calc
        inner x y = ∑ i : Fin 6, r * (x i * v i - c * (x i * x i)) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [y]
          ring
        _ = r * (inner x v - c * inner x x) := by
          unfold inner
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
        _ = 0 := by simp [hxx, c]
    have hW : wedge x y = p := by
      rw [← hw]
      funext k
      dsimp only [wedge, x, y]
      field_simp [hr.ne'] <;> ring
    have hyy : inner y y = 1 := by
      simpa [hW, hn, hxx, hxy] using (sqNorm_wedge x y).symm
    exact ⟨x, y, hxx, hyy, hxy, hW⟩
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    exact ⟨by simp [sqNorm_wedge, hu, hv, huv], pluecker_wedge u v⟩

end D5.S3.Quantum.Semigroups.WuTwoModeCliffordPluecker
