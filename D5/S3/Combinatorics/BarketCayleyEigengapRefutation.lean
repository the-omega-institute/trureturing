/- GID: D5/S3/Combinatorics/BarketCayleyEigengapRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/BarketCayleyEigengapRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/BarketCayleyEigengapRefutation.claim; result=D5/S3/Combinatorics/BarketCayleyEigengapRefutation.result; claim=D5/S3/Combinatorics/BarketCayleyEigengapRefutation.claim
   digest: Conjecture 4.4 fails for the Cayley 5-cycle on Z/5 with generator one. -/

/- proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #8688)
   Direct frozen dependencies: none (pinned Mathlib only). -/

import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.GroupTheory.Nilpotent

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Polynomial

namespace D5.S3.Combinatorics.BarketCayleyEigengapRefutation

/-- `L_N = D^{-1/2} L D^{-1/2}` entrywise: `L_ij / (sqrt d_i * sqrt d_j)`,
where `L = D - A` is Mathlib's `lapMatrix`. -/
noncomputable def normalizedLaplacian {V : Type} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) [DecidableRel graph.Adj] : Matrix V V Real :=
  fun i j => graph.lapMatrix Real i j /
    (Real.sqrt (graph.degree i) * Real.sqrt (graph.degree j))

/-- The same normalised Laplacian with the classically chosen decidable adjacency relation. -/
noncomputable def normalizedLaplacianClassical {V : Type} [Fintype V] [DecidableEq V]
    (graph : SimpleGraph V) : Matrix V V Real :=
  @normalizedLaplacian V _ _ graph (Classical.decRel _)

/-- The spectrum with multiplicity, sorted ascending: the real roots of the characteristic
polynomial. This is exact for normalised Laplacians, which are real symmetric matrices. -/
noncomputable def sortedSpectrum {V : Type} [Fintype V] [DecidableEq V]
    (matrix : Matrix V V Real) : List Real :=
  (matrix.charpoly.roots).sort (· <= ·)

/-- The 1-indexed eigenvalue of a sorted spectrum. -/
noncomputable def eig (spectrum : List Real) (i : Nat) : Real :=
  spectrum.getD (i - 1) 0

/-- Indices in the source range whose consecutive eigengap is greater than one. -/
noncomputable def conjectureGapSet {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (generators : Finset G) : Set Nat := by
  let spectrum := sortedSpectrum
    (normalizedLaplacianClassical (SimpleGraph.mulCayley (generators : Set G)))
  exact {i : Nat |
    1 <= i ∧ i <= Fintype.card G - 1 ∧
      eig spectrum (i + 1) - eig spectrum i > 1}

/-- Conjecture 4.4, with `k_{>1}` in hypothesis position. -/
def claim : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G], Group.IsNilpotent G ->
    ∀ generators : Finset G, Subgroup.closure (generators : Set G) = ⊤ ->
      ∀ k : Nat, IsLeast (conjectureGapSet generators) k ->
        k = Fintype.card G - 1 ∨
          ∃ j : Nat, 1 <= j ∧ j <= Group.nilpotencyClass G ∧
            k = Nat.card (G ⧸ Subgroup.upperCentralSeries G j)

private abbrev GFive := Multiplicative (Fin 5)

private def generatorSetFive : Set GFive := {Multiplicative.ofAdd 1}

private def gammaFive : SimpleGraph GFive :=
  SimpleGraph.mulCayley generatorSetFive

private instance instDecidableRelGammaFive : DecidableRel gammaFive.Adj := by
  intro u v
  have hAdj : gammaFive.Adj u v <->
      v = u * Multiplicative.ofAdd 1 ∨ u = v * Multiplicative.ofAdd 1 := by
    rw [gammaFive, SimpleGraph.mulCayley_adj']
    constructor
    · rintro ⟨_, ⟨a, ha, huv | huv⟩⟩
      · have ha1 : a = Multiplicative.ofAdd (1 : Fin 5) := by
          simpa [generatorSetFive] using ha
        exact Or.inl (ha1 ▸ huv.symm)
      · have ha1 : a = Multiplicative.ofAdd (1 : Fin 5) := by
          simpa [generatorSetFive] using ha
        exact Or.inr (ha1 ▸ huv)
    · intro h
      rcases h with h | h
      · refine ⟨?_, ⟨Multiplicative.ofAdd 1, by simp [generatorSetFive], Or.inl h.symm⟩⟩
        intro huv
        have hone : Multiplicative.ofAdd (1 : Fin 5) = (1 : GFive) := by
          apply mul_left_cancel (a := u)
          simpa using h.symm.trans huv.symm
        exact (by decide : Multiplicative.ofAdd (1 : Fin 5) ≠ (1 : GFive)) hone
      · refine ⟨?_, ⟨Multiplicative.ofAdd 1, by simp [generatorSetFive], Or.inr h⟩⟩
        intro huv
        have hone : Multiplicative.ofAdd (1 : Fin 5) = (1 : GFive) := by
          apply mul_left_cancel (a := v)
          simpa using h.symm.trans huv
        exact (by decide : Multiplicative.ofAdd (1 : Fin 5) ≠ (1 : GFive)) hone
  exact decidable_of_iff _ hAdj.symm

private def reindexFive : GFive ≃ Fin 5 := Multiplicative.toAdd

private noncomputable def normalizedFive : Matrix (Fin 5) (Fin 5) Real :=
  Matrix.reindex reindexFive reindexFive (normalizedLaplacian gammaFive)

private noncomputable def targetFive : Matrix (Fin 5) (Fin 5) Real := !![
  1, -(1 / 2 : Real), 0, 0, -(1 / 2 : Real);
  -(1 / 2 : Real), 1, -(1 / 2 : Real), 0, 0;
  0, -(1 / 2 : Real), 1, -(1 / 2 : Real), 0;
  0, 0, -(1 / 2 : Real), 1, -(1 / 2 : Real);
  -(1 / 2 : Real), 0, 0, -(1 / 2 : Real), 1]

private noncomputable def charMatrixFive : Matrix (Fin 5) (Fin 5) Real[X] := !![
  X - C 1, C (1 / 2 : Real), 0, 0, C (1 / 2 : Real);
  C (1 / 2 : Real), X - C 1, C (1 / 2 : Real), 0, 0;
  0, C (1 / 2 : Real), X - C 1, C (1 / 2 : Real), 0;
  0, 0, C (1 / 2 : Real), X - C 1, C (1 / 2 : Real);
  C (1 / 2 : Real), 0, 0, C (1 / 2 : Real), X - C 1]

private noncomputable def aFive : Real := (5 - Real.sqrt 5) / 4

private noncomputable def bFive : Real := (5 + Real.sqrt 5) / 4

private def generatorsFive : Finset GFive := {Multiplicative.ofAdd 1}

private def gapSetFive : Set Nat := {i : Nat |
  1 <= i ∧ i <= Fintype.card GFive - 1 ∧
    eig (sortedSpectrum (normalizedLaplacian gammaFive)) (i + 1) -
      eig (sortedSpectrum (normalizedLaplacian gammaFive)) i > 1}

example : gammaFive.Adj (Multiplicative.ofAdd (0 : Fin 5))
    (Multiplicative.ofAdd (1 : Fin 5)) := by decide

example : ¬ gammaFive.Adj (Multiplicative.ofAdd (0 : Fin 5))
    (Multiplicative.ofAdd (2 : Fin 5)) := by decide

example : gammaFive.degree (Multiplicative.ofAdd (0 : Fin 5)) = 2 := by decide

example : Group.nilpotencyClass (Multiplicative (ZMod 5)) = 1 := by
  have hle : Group.nilpotencyClass (Multiplicative (ZMod 5)) <= 1 :=
    CommGroup.nilpotencyClass_le_one
  have hne : Group.nilpotencyClass (Multiplicative (ZMod 5)) ≠ 0 := by
    intro hzero
    have hs : Subsingleton (Multiplicative (ZMod 5)) :=
      (Group.nilpotencyClass_zero_iff_subsingleton).mp hzero
    have : (0 : ZMod 5) = 1 := by
      apply Multiplicative.ofAdd.injective
      exact Subsingleton.elim _ _
    exact (by decide : (0 : ZMod 5) ≠ 1) this
  omega

example : Fintype.card (Multiplicative (ZMod 5)) - 1 = 4 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- The central-quotient eigengap conjecture is false. -/
theorem result : ¬ claim := by
  have charpoly_normalizedLaplacian_five :
    (normalizedLaplacian gammaFive).charpoly =
      (X : Real[X]) * (X ^ 2 - C (5 / 2 : Real) * X + C (5 / 4 : Real)) ^ 2 := by
    have hAdj (u v : GFive) : gammaFive.Adj u v <->
        v = u * Multiplicative.ofAdd 1 ∨ u = v * Multiplicative.ofAdd 1 := by
      rw [gammaFive, SimpleGraph.mulCayley_adj']
      constructor
      · rintro ⟨_, ⟨a, ha, huv | huv⟩⟩
        · have ha1 : a = Multiplicative.ofAdd (1 : Fin 5) := by
            simpa [generatorSetFive] using ha
          exact Or.inl (ha1 ▸ huv.symm)
        · have ha1 : a = Multiplicative.ofAdd (1 : Fin 5) := by
            simpa [generatorSetFive] using ha
          exact Or.inr (ha1 ▸ huv)
      · intro h
        rcases h with h | h
        · refine ⟨?_, ⟨Multiplicative.ofAdd 1, by simp [generatorSetFive], Or.inl h.symm⟩⟩
          intro huv
          have hone : Multiplicative.ofAdd (1 : Fin 5) = (1 : GFive) := by
            apply mul_left_cancel (a := u)
            simpa using h.symm.trans huv.symm
          exact (by decide : Multiplicative.ofAdd (1 : Fin 5) ≠ (1 : GFive)) hone
        · refine ⟨?_, ⟨Multiplicative.ofAdd 1, by simp [generatorSetFive], Or.inr h⟩⟩
          intro huv
          have hone : Multiplicative.ofAdd (1 : Fin 5) = (1 : GFive) := by
            apply mul_left_cancel (a := v)
            simpa using h.symm.trans huv
          exact (by decide : Multiplicative.ofAdd (1 : Fin 5) ≠ (1 : GFive)) hone
    have hDegree : ∀ u : GFive, gammaFive.degree u = 2 := by decide
    have hLapEntry (u v : GFive) : gammaFive.lapMatrix Real u v =
        (if u = v then 2 else 0) - (if gammaFive.Adj u v then 1 else 0) := by
      have hu := hDegree u
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
        Matrix.diagonal, hu]
    have hNormalizedEntry (u v : GFive) : normalizedLaplacian gammaFive u v =
        (if u = v then 1 else 0) - (if gammaFive.Adj u v then (1 / 2 : Real) else 0) := by
      rw [normalizedLaplacian]
      have hu := hDegree u
      have hv := hDegree v
      have hden : Real.sqrt (gammaFive.degree u) * Real.sqrt (gammaFive.degree v) = 2 := by
        rw [hu, hv, ← pow_two]
        norm_num [Real.sq_sqrt]
      rw [hden, hLapEntry]
      by_cases huv : u = v <;> by_cases hadj : gammaFive.Adj u v <;>
        simp [huv, hadj] <;> ring
    have hReindexApply (i : Fin 5) : reindexFive.symm i = Multiplicative.ofAdd i := by rfl
    have hOneNeTwo : (1 : GFive) ≠ Multiplicative.ofAdd (2 : Fin 5) := by decide
    have hOneNeThree : (1 : GFive) ≠ Multiplicative.ofAdd (3 : Fin 5) := by decide
    have hNormalizedFive : normalizedFive = targetFive := by
      ext i j
      rw [normalizedFive, Matrix.reindex_apply, Matrix.submatrix_apply, hNormalizedEntry]
      rw [hReindexApply, hReindexApply]
      fin_cases i <;> fin_cases j
      all_goals simp_rw [hAdj]
      all_goals simp [targetFive, ← ofAdd_add, Fin.ext_iff, hOneNeTwo, hOneNeThree] <;>
        norm_num <;> decide
    have hDetSparse {n : Nat}
        (matrix : Matrix (Fin (n + 2)) (Fin (n + 2)) Real[X])
        (hr : ∀ j : Fin n, matrix 0 j.succ.succ = 0)
        (hc : ∀ i : Fin n, matrix i.succ.succ 0 = 0) :
        matrix.det = matrix 0 0 * (matrix.submatrix Fin.succ Fin.succ).det -
          matrix 0 1 * matrix 1 0 *
            (matrix.submatrix (fun i : Fin n => i.succ.succ)
              (fun j : Fin n => j.succ.succ)).det := by
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.succ_zero_eq_one, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero,
        Fin.val_succ, hr, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      have hminor :
          (matrix.submatrix Fin.succ (1 : Fin (n + 2)).succAbove).det =
            matrix 1 0 * (matrix.submatrix (fun i : Fin n => i.succ.succ)
              (fun j : Fin n => j.succ.succ)).det := by
        rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Matrix.submatrix_apply]
        have hzero : (1 : Fin (n + 2)).succAbove 0 = 0 := by simp
        rw [hzero]
        simp only [hc, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
        congr 2
      rw [hminor]
      norm_num [Fin.val_one']
      ring
    have hDetFourTwo (matrix : Matrix (Fin 4) (Fin 4) Real[X])
        (h2 : matrix 0 2 = 0) (h3 : matrix 0 3 = 0) :
        matrix.det = matrix 0 0 * (matrix.submatrix Fin.succ Fin.succ).det -
          matrix 0 1 * (matrix.submatrix Fin.succ (1 : Fin 4).succAbove).det := by
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.val_succ,
        h2, h3, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.succAbove_zero, Fin.val_succ, h2, h3,
        mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      have h2' : matrix 0 (2 : Fin 4) = 0 := h2
      have h3' : matrix 0 (3 : Fin 4) = 0 := h3
      simp [h2', h3', Fin.ext_iff]
      ring
    have hDetThreeFront (matrix : Matrix (Fin 5) (Fin 5) Real[X])
        (h2 : matrix 0 2 = 0) (h3 : matrix 0 3 = 0) :
        matrix.det = matrix 0 0 * (matrix.submatrix Fin.succ Fin.succ).det -
          matrix 0 1 * (matrix.submatrix Fin.succ (1 : Fin 5).succAbove).det +
          matrix 0 4 * (matrix.submatrix Fin.succ (4 : Fin 5).succAbove).det := by
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.val_succ,
        mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
      have h20 : matrix 0 (Fin.succ 0).succ = 0 := by simpa [Fin.ext_iff] using h2
      have h30 : matrix 0 (Fin.succ 0).succ.succ = 0 := by simpa [Fin.ext_iff] using h3
      simp [h2, h3, h20, h30, Fin.ext_iff]
      ring
    have hDetFourThree (matrix : Matrix (Fin 4) (Fin 4) Real[X])
        (h3 : matrix 0 3 = 0) :
        matrix.det = matrix 0 0 * (matrix.submatrix Fin.succ Fin.succ).det -
          matrix 0 1 * (matrix.submatrix Fin.succ (1 : Fin 4).succAbove).det +
          matrix 0 2 * (matrix.submatrix Fin.succ (2 : Fin 4).succAbove).det := by
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.val_succ,
        mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have h30 : matrix 0 (Fin.succ 0).succ.succ = 0 := by simpa [Fin.ext_iff] using h3
      simp [h3, h30, Fin.ext_iff]
      ring
    have hCharMatrixDet : charMatrixFive.det =
        (X : Real[X]) * (X ^ 2 - C (5 / 2 : Real) * X + C (5 / 4 : Real)) ^ 2 := by
      let d : Real[X] := X - C 1
      let c : Real[X] := C (1 / 2 : Real)
      have hdet0 : (charMatrixFive.submatrix Fin.succ Fin.succ).det =
          d ^ 4 - 3 * d ^ 2 * c ^ 2 + c ^ 4 := by
        rw [hDetSparse (matrix := charMatrixFive.submatrix Fin.succ Fin.succ)
          (by intro j; fin_cases j <;> simp [charMatrixFive, Matrix.submatrix_apply, Fin.succAbove])
          (by intro i; fin_cases i <;> simp [charMatrixFive, Matrix.submatrix_apply, Fin.succAbove])]
        simp only [d, c]
        simp [charMatrixFive, Matrix.submatrix_apply, Fin.succAbove, Matrix.det_fin_three,
          Matrix.det_fin_two]
        ring
      have hdet1 : (charMatrixFive.submatrix Fin.succ (1 : Fin 5).succAbove).det =
          c * d ^ 3 - 2 * d * c ^ 3 - c ^ 4 := by
        rw [hDetFourTwo (matrix := charMatrixFive.submatrix Fin.succ (1 : Fin 5).succAbove)
          (by simp [charMatrixFive, Matrix.submatrix_apply, Fin.succAbove])
          (by simp [charMatrixFive, Matrix.submatrix_apply, Fin.succAbove])]
        simp only [d, c]
        simp [charMatrixFive, Matrix.submatrix_apply, Fin.succAbove, Matrix.det_fin_three,
          Matrix.det_fin_two]
        ring
      have hdet4 : (charMatrixFive.submatrix Fin.succ (4 : Fin 5).succAbove).det =
          c ^ 4 - c * d ^ 3 + 2 * c ^ 3 * d := by
        rw [hDetFourThree (matrix := charMatrixFive.submatrix Fin.succ (4 : Fin 5).succAbove)
          (by simp [charMatrixFive, Matrix.submatrix_apply, Fin.succAbove])]
        simp only [d, c]
        simp [charMatrixFive, Matrix.submatrix_apply, Fin.succAbove, Matrix.det_fin_three,
          Matrix.det_fin_two]
        ring
      rw [hDetThreeFront (matrix := charMatrixFive) (by simp [charMatrixFive])
        (by simp [charMatrixFive]), hdet0, hdet1, hdet4]
      have h52 : (C (5 / 2 : Real) : Real[X]) = 5 * c := by
        rw [show c = C (1 / 2 : Real) by rfl, ← Polynomial.C_ofNat 5, ← Polynomial.C_mul]
        norm_num [Polynomial.C_ofNat]
      have h54 : (C (5 / 4 : Real) : Real[X]) = 5 * c ^ 2 := by
        rw [show c = C (1 / 2 : Real) by rfl, ← Polynomial.C_pow]
        rw [← Polynomial.C_ofNat 5, ← Polynomial.C_mul]
        norm_num [Polynomial.C_ofNat]
      rw [h52, h54]
      simp only [charMatrixFive, Matrix.submatrix_apply, Fin.succAbove]
      dsimp [d]
      simp only [Polynomial.C_1]
      rw [show (C (1 / 2 : Real) : Real[X]) = c by rfl]
      ring_nf
      have hc : 2 * c = (1 : Real[X]) := by
        dsimp [c]
        rw [← Polynomial.C_ofNat 2, ← Polynomial.C_mul]
        norm_num [Polynomial.C_ofNat]
      linear_combination
        (c ^ 4 - 10 * c ^ 3 * X - 2 * c ^ 3 + 25 * c ^ 2 * X ^ 2 -
          5 * c ^ 2 * X - c ^ 2 - 20 * c * X ^ 3 + 20 * c * X ^ 2 -
          10 * c * X + 2 * c + 5 * X ^ 4 - 10 * X ^ 3 + 10 * X ^ 2 -
          5 * X + 1) * hc
    have hCharpolyTarget : targetFive.charpoly =
        (X : Real[X]) * (X ^ 2 - C (5 / 2 : Real) * X + C (5 / 4 : Real)) ^ 2 := by
      have hCharmatrix : Matrix.charmatrix targetFive = charMatrixFive := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.charmatrix, targetFive, charMatrixFive, Matrix.scalar, Matrix.diagonal]
      rw [Matrix.charpoly, hCharmatrix, hCharMatrixDet]
    calc
      (normalizedLaplacian gammaFive).charpoly = normalizedFive.charpoly :=
        (Matrix.charpoly_reindex reindexFive (normalizedLaplacian gammaFive)).symm
      _ = targetFive.charpoly := by rw [hNormalizedFive]
      _ = _ := hCharpolyTarget

  have sortedSpectrum_normalizedLaplacian_five :
    sortedSpectrum (normalizedLaplacian gammaFive) =
      [0, aFive, aFive, bFive, bFive] := by
    have hSqrtSq : (Real.sqrt (5 : Real)) ^ 2 = 5 := by
      norm_num [Real.sq_sqrt]
    have hQuadFactor :
        (X ^ 2 - C (5 / 2 : Real) * X + C (5 / 4 : Real) : Real[X]) =
          (X - C aFive) * (X - C bFive) := by
      have hsum : C aFive + C bFive = (C (5 / 2 : Real) : Real[X]) := by
        rw [← C_add]
        dsimp [aFive, bFive]
        congr 1
        ring
      have hprod : C aFive * C bFive = (C (5 / 4 : Real) : Real[X]) := by
        rw [← C_mul]
        dsimp [aFive, bFive]
        congr 1
        nlinarith [hSqrtSq]
      calc
        (X ^ 2 - C (5 / 2 : Real) * X + C (5 / 4 : Real) : Real[X]) =
            X ^ 2 - (C aFive + C bFive) * X + C aFive * C bFive := by
              rw [hsum, hprod]
        _ = (X - C aFive) * (X - C bFive) := by ring
    have hRootsPolynomial :
        ((X : Real[X]) * (X ^ 2 - C (5 / 2 : Real) * X + C (5 / 4 : Real)) ^ 2).roots =
          ({0, aFive, aFive, bFive, bFive} : Multiset Real) := by
      classical
      rw [hQuadFactor]
      rw [Polynomial.roots_mul
        (mul_ne_zero Polynomial.X_ne_zero
          (pow_ne_zero _ (mul_ne_zero (Polynomial.X_sub_C_ne_zero aFive)
            (Polynomial.X_sub_C_ne_zero bFive))))]
      rw [Polynomial.roots_pow]
      rw [Polynomial.roots_mul
        (mul_ne_zero (Polynomial.X_sub_C_ne_zero aFive)
          (Polynomial.X_sub_C_ne_zero bFive))]
      simp only [Polynomial.roots_X, Polynomial.roots_X_sub_C]
      rw [two_nsmul]
      change (({(0 : Real)} : Multiset Real) +
        (({aFive} + {bFive}) + ({aFive} + {bFive}))) =
          (({(0 : Real)} : Multiset Real) + {aFive} + {aFive} + {bFive} + {bFive})
      ac_rfl
    have hRoots : (normalizedLaplacian gammaFive).charpoly.roots =
        ({0, aFive, aFive, bFive, bFive} : Multiset Real) := by
      rw [charpoly_normalizedLaplacian_five, hRootsPolynomial]
    have hSqrtPos : 0 < Real.sqrt (5 : Real) := Real.sqrt_pos.2 (by norm_num)
    have hSqrtOne : 1 <= Real.sqrt (5 : Real) := by nlinarith [hSqrtSq, hSqrtPos]
    have hSqrtFive : Real.sqrt (5 : Real) < 5 := by nlinarith [hSqrtSq, hSqrtPos]
    have hAPos : 0 < aFive := by dsimp [aFive]; nlinarith [hSqrtFive]
    have hALeB : aFive <= bFive := by dsimp [aFive, bFive]; nlinarith [hSqrtPos]
    have hBPos : 0 < bFive := by dsimp [bFive]; nlinarith [hSqrtPos]
    rw [sortedSpectrum, hRoots]
    rw [show ({0, aFive, aFive, bFive, bFive} : Multiset Real) =
        (0 : Real) ::ₘ {aFive, aFive, bFive, bFive} by rfl]
    rw [Multiset.sort_cons]
    · rw [show ({aFive, aFive, bFive, bFive} : Multiset Real) =
        aFive ::ₘ {aFive, bFive, bFive} by rfl]
      rw [Multiset.sort_cons]
      · rw [show ({aFive, bFive, bFive} : Multiset Real) =
          aFive ::ₘ {bFive, bFive} by rfl]
        rw [Multiset.sort_cons]
        · rw [show ({bFive, bFive} : Multiset Real) = bFive ::ₘ {bFive} by rfl]
          rw [Multiset.sort_cons]
          · simp
          · simp
        · simp [hALeB]
      · simp [hALeB]
    · simp [hAPos.le, hBPos.le]

  intro hclaim
  have hGenerates : Subgroup.closure (generatorSetFive : Set GFive) = ⊤ := by
    apply top_unique
    intro x hx
    change x ∈ Subgroup.closure ({Multiplicative.ofAdd 1} : Set GFive)
    rw [Subgroup.mem_closure_singleton]
    fin_cases x
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨2, by decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨4, by decide⟩
  have hSet : (generatorsFive : Set GFive) = generatorSetFive := by
    ext x
    simp [generatorsFive, generatorSetFive]
  have hNormalizedClassical :
      normalizedLaplacianClassical gammaFive = normalizedLaplacian gammaFive := by
    change @normalizedLaplacian GFive _ _ gammaFive (Classical.decRel _) =
      @normalizedLaplacian GFive _ _ gammaFive
        (inferInstance : DecidableRel gammaFive.Adj)
    rw [Subsingleton.elim (Classical.decRel gammaFive.Adj)
      (inferInstance : DecidableRel gammaFive.Adj)]
  have hGapSet : conjectureGapSet generatorsFive = gapSetFive := by
    unfold conjectureGapSet gapSetFive
    rw [hSet]
    change {i : Nat |
        1 <= i ∧ i <= Fintype.card GFive - 1 ∧
          eig (sortedSpectrum (normalizedLaplacianClassical gammaFive)) (i + 1) -
            eig (sortedSpectrum (normalizedLaplacianClassical gammaFive)) i > 1} = _
    rw [hNormalizedClassical]
  have hSqrtSq : (Real.sqrt (5 : Real)) ^ 2 = 5 := by
    norm_num [Real.sq_sqrt]
  have hSqrtPos : 0 < Real.sqrt (5 : Real) := Real.sqrt_pos.2 (by norm_num)
  have hSqrtOne : 1 <= Real.sqrt (5 : Real) := by nlinarith [hSqrtSq, hSqrtPos]
  have hSqrtTwo : 2 < Real.sqrt (5 : Real) := by nlinarith [hSqrtSq, hSqrtPos]
  have hALeOne : aFive <= 1 := by dsimp [aFive]; nlinarith [hSqrtOne]
  have hLeastGap : IsLeast gapSetFive 3 := by
    constructor
    · rw [gapSetFive]
      rw [show Fintype.card GFive = 5 by decide]
      rw [sortedSpectrum_normalizedLaplacian_five]
      simp only [Set.mem_ofPred_eq]
      refine ⟨by norm_num, by norm_num, ?_⟩
      simp [eig, aFive, bFive]
      nlinarith [hSqrtTwo]
    · intro i hi
      rw [gapSetFive] at hi
      rw [show Fintype.card GFive = 5 by decide] at hi
      rcases hi with ⟨hi1, hi4, higap⟩
      have ha := hALeOne
      dsimp [aFive] at ha
      interval_cases i <;>
        simp [sortedSpectrum_normalizedLaplacian_five, eig, aFive, bFive] at higap ⊢ <;>
        nlinarith [ha]
  have hLeast : IsLeast (conjectureGapSet generatorsFive) 3 := by
    rw [hGapSet]
    exact hLeastGap
  have hCases := hclaim GFive CommGroup.isNilpotent generatorsFive
    (by simpa [hSet] using hGenerates) 3 hLeast
  rcases hCases with hlast | ⟨j, hj1, hjc, hjcard⟩
  · have hcard : Fintype.card GFive = 5 := by decide
    omega
  · have hClass : Group.nilpotencyClass GFive = 1 := by
      have hle : Group.nilpotencyClass GFive <= 1 :=
        CommGroup.nilpotencyClass_le_one
      have hne : Group.nilpotencyClass GFive ≠ 0 := by
        intro hzero
        have hs : Subsingleton GFive :=
          (Group.nilpotencyClass_zero_iff_subsingleton).mp hzero
        have heq : (0 : Fin 5) = 1 := by
          apply Multiplicative.ofAdd.injective
          exact Subsingleton.elim _ _
        exact (by decide : (0 : Fin 5) ≠ 1) heq
      omega
    have hUpper : Subgroup.upperCentralSeries GFive 1 = ⊤ := by
      rw [Subgroup.upperCentralSeries_one, CommGroup.center_eq_top]
    have hQuotient : Nat.card (GFive ⧸ Subgroup.upperCentralSeries GFive 1) = 1 := by
      rw [hUpper]
      exact Nat.card_eq_one_iff_unique.mpr
        ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
    have hj : j = 1 := by omega
    subst j
    omega

#print axioms result

end D5.S3.Combinatorics.BarketCayleyEigengapRefutation
