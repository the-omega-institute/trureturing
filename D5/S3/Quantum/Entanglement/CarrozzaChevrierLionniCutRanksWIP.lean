/- GID: D5/S3/Quantum/Entanglement/CarrozzaChevrierLionniCutRanksWIP
   generality: G
   mirror-B: none(waiver:open-problem-stage-a)
   mirror-E: none(waiver:stage-a-open)
   anchors: []
   utility: none
   digest: Cut-rank invariance under local isometries and regrouped products. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor
import D5.S3.Quantum.Recovery.PurifiedLocalPath
import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-! Cut-rank identities for finite complex tensors and their local isometric embeddings. -/

compile_only_with_mathlib
set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.CarrozzaChevrierLionniCutRanksWIP

open Matrix Module
open scoped TensorProduct Kronecker
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (productMap)
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor
  (rectangle_finrank)

theorem rank_kronecker {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q] (A : Matrix m n ℂ) (B : Matrix p q ℂ) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  rw [rank_eq_finrank_range_toLin _
    ((Pi.basisFun ℂ m).tensorProduct (Pi.basisFun ℂ p))
    ((Pi.basisFun ℂ n).tensorProduct (Pi.basisFun ℂ q)), Matrix.toLin_kronecker]
  change finrank ℂ (LinearMap.range (TensorProduct.map A.mulVecLin B.mulVecLin)) = _
  rw [TensorProduct.range_map]
  exact rectangle_finrank _ _

/-- Matrix rank multiplies over a finite product of rectangular matrices. -/
theorem rank_productMap (k : ℕ)
    (m n : Fin k → Type) [∀ i, Fintype (m i)] [∀ i, Fintype (n i)]
    (A : ∀ i, Matrix (m i) (n i) ℂ) :
    (productMap n A).rank = ∏ i, (A i).rank := by
  classical
  induction k with
  | zero =>
    let trivial (t : Fin 0 → Type) : Unit ≃ (∀ i, t i) :=
      ⟨fun _ i => Fin.elim0 i, fun _ => (), fun _ => rfl, fun _ => Subsingleton.elim _ _⟩
    have h : (productMap n A).submatrix (trivial m) (trivial n) =
        (1 : Matrix Unit Unit ℂ) := by
      ext u v
      simp [productMap, Matrix.one_apply, Subsingleton.elim u v]
    rw [← Matrix.rank_submatrix _ (trivial m) (trivial n), h, Matrix.rank_one]
    simp
  | succ k ih =>
    let m' := fun i : Fin k => m i.succ
    let n' := fun i : Fin k => n i.succ
    let A' : ∀ i, Matrix (m' i) (n' i) ℂ := fun i => A i.succ
    have h : (productMap n A).submatrix (Fin.consEquiv m) (Fin.consEquiv n) =
        A 0 ⊗ₖ productMap n' A' := by
      ext ⟨u, us⟩ ⟨v, vs⟩
      simp [productMap, Fin.prod_univ_succ, A']
    rw [← Matrix.rank_submatrix _ (Fin.consEquiv m) (Fin.consEquiv n), h,
      rank_kronecker, ih m' n' A', Fin.prod_univ_succ]

/-- Grouping local coordinate labels on the two sides of a cut. -/
def flatten {I : Type*} (s : I → Prop) [DecidablePred s] {d : I → Type*}
    (ψ : (∀ i, d i) → ℂ) :
    Matrix (∀ i : {i // s i}, d i) (∀ i : {i // ¬s i}, d i) ℂ :=
  fun u v => ψ ((Equiv.piEquivPiSubtypeProd s d).symm (u, v))

private theorem productMap_gram {I : Type*} [Fintype I] [DecidableEq I]
    {d e : I → Type*} [∀ i, Fintype (e i)] [∀ i, DecidableEq (d i)]
    (U : ∀ i, Matrix (e i) (d i) ℂ) (hU : ∀ i, (U i)ᴴ * U i = 1) :
    (productMap d U)ᴴ * productMap d U = 1 := by
  ext x y
  calc
    _ = ∏ i, ((U i)ᴴ * U i) (x i) (y i) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, productMap, star_prod,
        ← Finset.prod_mul_distrib, Fintype.prod_sum]
    _ = _ := by
      simp only [hU, Matrix.one_apply]
      by_cases hxy : x = y
      · subst y
        simp
      · rw [if_neg hxy]
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
          by_contra! hn
          exact hxy (funext hn)
        exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- A left inverse and a right inverse recover the original flattening. -/
theorem rank_mul_transpose_of_isometries {m n p q : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (L : Matrix p m ℂ) (R : Matrix q n ℂ)
    (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1) :
    (L * A * Rᵀ).rank = A.rank := by
  let B := L * A * Rᵀ
  have hRight : Rᵀ * (Rᴴ)ᵀ = 1 := by
    rw [← transpose_mul, hR, transpose_one]
  have hA : Lᴴ * B * (Rᴴ)ᵀ = A := by
    calc
      _ = (Lᴴ * L) * A * (Rᵀ * (Rᴴ)ᵀ) := by dsimp [B]; simp only [Matrix.mul_assoc]
      _ = A := by rw [hL, hRight, Matrix.one_mul, Matrix.mul_one]
  exact le_antisymm
    ((rank_mul_le_left (L * A) Rᵀ).trans (rank_mul_le_right L A))
    ((congrArg Matrix.rank hA).ge.trans
      ((rank_mul_le_left (Lᴴ * B) (Rᴴ)ᵀ).trans (rank_mul_le_right Lᴴ B)))

/-- Applying a matrix at each party acts on a cut by its two grouped matrices. -/
theorem flatten_localImage {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → Prop) [DecidablePred s]
    {d e : I → Type*} [∀ i, Fintype (d i)]
    (ψ : (∀ i, d i) → ℂ) (U : ∀ i, Matrix (e i) (d i) ℂ) :
    flatten s (productMap d U *ᵥ ψ) =
      productMap (fun i : {i // s i} => d i) (fun i => U i) * flatten s ψ *
        (productMap (fun i : {i // ¬s i} => d i) (fun i => U i))ᵀ := by
  classical
  let E := Equiv.piEquivPiSubtypeProd s d
  apply Matrix.ext
  intro z w
  let v := (Equiv.piEquivPiSubtypeProd s e).symm (z, w)
  let L (x : ∀ i : {i // s i}, d i) := ∏ i : {i // s i}, U i (z i) (x i)
  let R (y : ∀ i : {i // ¬s i}, d i) := ∏ i : {i // ¬s i}, U i (w i) (y i)
  change (∑ x, (∏ i, U i (v i) (x i)) * ψ x) = _
  calc
    _ = ∑ x : (∀ i : {i // s i}, d i) × (∀ i : {i // ¬s i}, d i),
        L x.1 * ψ (E.symm x) * R x.2 := by
      refine (Fintype.sum_equiv E.symm _ _ ?_).symm
      rintro ⟨x, y⟩
      change L x * ψ (E.symm (x, y)) * R y =
        (∏ i, U i (v i) (E.symm (x, y) i)) * ψ (E.symm (x, y))
      rw [← Fintype.prod_subtype_mul_prod_subtype s
        (fun i => U i (v i) (E.symm (x, y) i))]
      have hl : (∏ i : {i // s i}, U i (v i) (E.symm (x, y) i)) = L x := by
        apply Finset.prod_congr rfl
        intro i _
        simp [v, E, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
      have hr : (∏ i : {i // ¬s i}, U i (v i) (E.symm (x, y) i)) = R y := by
        apply Finset.prod_congr rfl
        intro i _
        simp [v, E, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
      rw [hl, hr]
      ring
    _ = _ := by
      simp only [Fintype.sum_prod_type, Matrix.mul_apply, Finset.sum_mul,
        Matrix.transpose_apply, productMap, flatten, L, R, E]
      exact Finset.sum_comm

theorem flatten_rank_local_isometries {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → Prop) [DecidablePred s]
    {d e : I → Type*} [∀ i, Fintype (d i)] [∀ i, Fintype (e i)]
    [∀ i, DecidableEq (d i)]
    (ψ : (∀ i, d i) → ℂ) (U : ∀ i, Matrix (e i) (d i) ℂ)
    (hU : ∀ i, (U i)ᴴ * U i = 1) :
    (flatten s (productMap d U *ᵥ ψ)).rank = (flatten s ψ).rank := by
  classical
  rw [flatten_localImage]
  exact rank_mul_transpose_of_isometries _ _ _
    (productMap_gram _ fun i => hU i) (productMap_gram _ fun i => hU i)

/-- Across a party cut, regrouping product factors just transposes the two index arrays. -/
theorem flatten_rank_grouped {I : Type} [Fintype I] [DecidableEq I] (s : I → Prop) [DecidablePred s]
    (k : ℕ) (d : Fin k → I → Type) [∀ j i, Fintype (d j i)]
    (ψ : ∀ j, (∀ i, d j i) → ℂ) :
    (flatten (d := fun i => ∀ j, d j i) s (fun x => ∏ j, ψ j (fun i => x i j))).rank =
      ∏ j, (flatten s (ψ j)).rank := by
  classical
  let row := Equiv.piComm (fun (j : Fin k) (i : {i // s i}) => d j i)
  let col := Equiv.piComm (fun (j : Fin k) (i : {i // ¬s i}) => d j i)
  let A := flatten (d := fun i => ∀ j, d j i) s (fun x => ∏ j, ψ j (fun i => x i j))
  have h : A.submatrix row col =
      productMap (fun j => ∀ i : {i // ¬s i}, d j i) (fun j => flatten s (ψ j)) := by
    ext u v
    simp only [A, Matrix.submatrix_apply, flatten, productMap]
    apply Finset.prod_congr rfl
    intro j _
    apply congrArg (ψ j)
    funext i
    by_cases hi : s i <;>
      simp [row, col, Equiv.piComm, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  change A.rank = _
  rw [← Matrix.rank_submatrix A row col, h, rank_productMap]

end D5.S3.Quantum.Entanglement.CarrozzaChevrierLionniCutRanksWIP
