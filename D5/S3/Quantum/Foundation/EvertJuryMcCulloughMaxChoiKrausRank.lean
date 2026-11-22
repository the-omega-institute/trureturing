import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation

/-!
# Maximum Choi–Kraus rank of a matrix product with a unit

Question 1 of Eric Evert, Michael T. Jury and Scott McCullough,
*Completely Positive Matrix Products*, arXiv:2607.13251v1.
The construction and statement are from the preregistration in trureturing issue 29866.
-/

namespace D5.S3.Quantum.Foundation.EvertJuryMcCulloughMaxChoiKrausRank

open scoped BigOperators ComplexOrder

abbrev CMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The Introduction's complex bilinear matrix product, with input n and output m. -/
abbrev MatrixProduct (n m : ℕ) := CMatrix n →ₗ[ℂ] CMatrix n →ₗ[ℂ] CMatrix m

/-- The (i,j)-block of a matrix in M_ell(M_n), indexed by (block, coordinate). -/
def block {n ell : ℕ} (A : Matrix (Fin ell × Fin n) (Fin ell × Fin n) ℂ)
    (i j : Fin ell) : CMatrix n :=
  fun a b => A (i, a) (j, b)

/-- Equation (2.1): the block matrix with blocks Phi(A_ij,B_st). -/
def jointAmplification {n m ell : ℕ} (Phi : MatrixProduct n m)
    (A B : Matrix (Fin ell × Fin n) (Fin ell × Fin n) ℂ) :
    Matrix ((Fin ell × Fin ell) × Fin m) ((Fin ell × Fin ell) × Fin m) ℂ :=
  fun x y => Phi (block A x.1.1 y.1.1) (block B x.1.2 y.1.2) x.2 y.2

/-- Joint complete positivity as defined in the Introduction and Section 2. -/
def IsJointlyCompletelyPositive {n m : ℕ} (Phi : MatrixProduct n m) : Prop :=
  ∀ ell : ℕ, 1 ≤ ell →
    ∀ A B : Matrix (Fin ell × Fin n) (Fin ell × Fin n) ℂ,
      A.PosSemidef → B.PosSemidef → (jointAmplification Phi A B).PosSemidef

/-- Theorem 2.1(iii), with N coefficients of shape n^2 by m. -/
def HasKrausRepresentation {n m : ℕ} (Phi : MatrixProduct n m) (N : ℕ) : Prop :=
  ∃ V : Fin N → Matrix (Fin n × Fin n) (Fin m) ℂ,
    ∀ A B : CMatrix n,
      Phi A B = ∑ k : Fin N,
        (V k).conjTranspose * (Matrix.kronecker A B) * V k

/-- Remark 2.2's minimum number of coefficients; top outside the representable class. -/
noncomputable def choiKrausRank {n m : ℕ} (Phi : MatrixProduct n m) : ℕ∞ :=
  sInf {r : ℕ∞ | ∃ N : ℕ, r = (N : ℕ∞) ∧ HasKrausRepresentation Phi N}

/-- The source Choi convention, indexed (input, input, output). -/
def choiMatrix {n m : ℕ} (Phi : MatrixProduct n m) :
    Matrix ((Fin n × Fin n) × Fin m) ((Fin n × Fin n) × Fin m) ℂ :=
  fun x y => Phi (Matrix.single x.1.1 y.1.1 1)
    (Matrix.single x.1.2 y.1.2 1) x.2 y.2

/-- Section 5.3: Phi(L,Y)=Y for every Y. No positivity condition on L. -/
def IsLeftUnit {n : ℕ} (Phi : MatrixProduct n n) (L : CMatrix n) : Prop :=
  ∀ Y : CMatrix n, Phi L Y = Y

/-- Section 5.3: Phi(X,R)=X for every X. -/
def IsRightUnit {n : ℕ} (Phi : MatrixProduct n n) (R : CMatrix n) : Prop :=
  ∀ X : CMatrix n, Phi X R = X

/-- Section 5.3: one matrix is simultaneously a left and right unit. -/
def IsUnit {n : ℕ} (Phi : MatrixProduct n n) (T : CMatrix n) : Prop :=
  IsLeftUnit Phi T ∧ IsRightUnit Phi T

/-- Question 1 answered by n^3, for m=n and every positive integer n:
    each of the two classes has that upper bound and attains it. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ((∀ Phi : MatrixProduct n n, IsJointlyCompletelyPositive Phi →
        (∃ L : CMatrix n, IsLeftUnit Phi L) →
        choiKrausRank Phi ≤ ((n ^ 3 : ℕ) : ℕ∞)) ∧
      (∃ Phi : MatrixProduct n n, IsJointlyCompletelyPositive Phi ∧
        (∃ L : CMatrix n, IsLeftUnit Phi L) ∧
        choiKrausRank Phi = ((n ^ 3 : ℕ) : ℕ∞))) ∧
    ((∀ Phi : MatrixProduct n n, IsJointlyCompletelyPositive Phi →
        (∃ T : CMatrix n, IsUnit Phi T) →
        choiKrausRank Phi ≤ ((n ^ 3 : ℕ) : ℕ∞)) ∧
      (∃ Phi : MatrixProduct n n, IsJointlyCompletelyPositive Phi ∧
        (∃ T : CMatrix n, IsUnit Phi T) ∧
        choiKrausRank Phi = ((n ^ 3 : ℕ) : ℕ∞)))


open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)

noncomputable section

private abbrev Input (n : ℕ) := Fin n × Fin n
private abbrev SourceIndex (n m : ℕ) := Input n × Fin m
private abbrev D5Index (n m : ℕ) := Fin m × Input n

private def d5Choi {n m : ℕ} (Phi : MatrixProduct n m) :
    Matrix (D5Index n m) (D5Index n m) ℂ :=
  Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (choiMatrix Phi)

private def linearization {n m : ℕ} (Phi : MatrixProduct n m) :
    MatrixMap (Input n) (Fin m) ℂ :=
  MatrixMap.of_choi_matrix (d5Choi Phi)

private theorem linearization_single {n m : ℕ} (Phi : MatrixProduct n m)
    (i j s t : Fin n) :
    linearization Phi (single (i, s) (j, t) 1) = Phi (single i j 1) (single s t 1) := by
  ext a b
  change (∑ x : Input n, ∑ y : Input n,
    single (i, s) (j, t) (1 : ℂ) x y * d5Choi Phi (a, x) (b, y)) = _
  simp [Matrix.single, d5Choi, choiMatrix, Matrix.reindex_apply]

private theorem linearization_kronecker {n m : ℕ} (Phi : MatrixProduct n m)
    (A B : CMatrix n) : linearization Phi (Matrix.kronecker A B) = Phi A B := by
  let F : MatrixProduct n m :=
    (linearization Phi).compRight.comp (Matrix.kroneckerBilinear ℂ ℂ)
  have hF : F = Phi := by
    apply (Matrix.stdBasis ℂ (Fin n) (Fin n)).ext
    rintro ⟨i, j⟩
    apply (Matrix.stdBasis ℂ (Fin n) (Fin n)).ext
    rintro ⟨s, t⟩
    simp only [Matrix.stdBasis_eq_single]
    change linearization Phi (Matrix.kronecker (single i j 1) (single s t 1)) = _
    rw [Matrix.single_kronecker_single, one_mul, linearization_single]
  exact congrArg (fun G : MatrixProduct n m => G A B) hF

private theorem d5Choi_linearization {n m : ℕ} (Phi : MatrixProduct n m) :
    MatrixMap.choi_matrix (linearization Phi) = d5Choi Phi := by
  ext ⟨a, i, s⟩ ⟨b, j, t⟩
  change linearization Phi (single (i, s) (j, t) 1) a b = _
  rw [linearization_single]
  rfl

private theorem linearization_eq_kraus {n m N : ℕ} {Phi : MatrixProduct n m}
    (V : Fin N → Matrix (Input n) (Fin m) ℂ)
    (hV : ∀ A B, Phi A B = ∑ k, (V k).conjTranspose * Matrix.kronecker A B * V k) :
    linearization Phi = MatrixMap.of_kraus (fun k => (V k).conjTranspose)
      (fun k => (V k).conjTranspose) := by
  apply (Matrix.stdBasis ℂ (Input n) (Input n)).ext
  rintro ⟨⟨i, s⟩, ⟨j, t⟩⟩
  rw [Matrix.stdBasis_eq_single, linearization_single, hV, Matrix.single_kronecker_single, one_mul]
  simp [MatrixMap.of_kraus, LinearMap.sum_apply]

private theorem psd_has_kraus {n m : ℕ} {Phi : MatrixProduct n m}
    (h : (choiMatrix Phi).PosSemidef) :
    HasKrausRepresentation Phi (Fintype.card (D5Index n m)) := by
  classical
  have hD : (d5Choi Phi).PosSemidef := h.submatrix (Equiv.prodComm _ _)
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_PSD (d5Choi Phi) hD
  have hlin : linearization Phi = MatrixMap.of_kraus K K :=
    MatrixMap.choi_matrix_inj ((d5Choi_linearization Phi).trans hK)
  let e := Fintype.equivFin (D5Index n m)
  refine ⟨fun k => (K (e.symm k)).conjTranspose, fun A B => ?_⟩
  rw [← linearization_kronecker, hlin]
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.conjTranspose_conjTranspose]
  exact (Equiv.sum_comp e.symm _).symm

private theorem jcp_choi_psd {n m : ℕ} {Phi : MatrixProduct n m}
    (hn : 1 ≤ n) (h : IsJointlyCompletelyPositive Phi) : (choiMatrix Phi).PosSemidef := by
  let u : Input n → ℂ := fun x => if x.1 = x.2 then 1 else 0
  let Q := Matrix.vecMulVec u (star u)
  have hQ : Q.PosSemidef := Matrix.posSemidef_vecMulVec_self_star u
  have hblock (i j : Fin n) : block Q i j = single i j 1 := by
    ext a b
    by_cases hi : i = a <;> by_cases hj : j = b <;>
      simp [block, Q, u, vecMulVec, Matrix.single, hi, hj]
  have hC : jointAmplification Phi Q Q = choiMatrix Phi := by
    ext x y
    simp only [jointAmplification, hblock, choiMatrix]
  exact hC ▸ h n hn Q Q hQ hQ

private theorem sandwich_entries {n m ell : ℕ}
    (A B : Matrix (Fin ell × Fin n) (Fin ell × Fin n) ℂ)
    (V : Matrix (Input n) (Fin m) ℂ) :
    let Q : Matrix ((Fin ell × Fin ell) × Input n) ((Fin ell × Fin ell) × Input n) ℂ :=
      Matrix.reindex (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)
        (Matrix.kronecker A B)
    let D : Matrix ((Fin ell × Fin ell) × Input n) ((Fin ell × Fin ell) × Fin m) ℂ :=
      Matrix.kronecker (1 : Matrix (Fin ell × Fin ell) (Fin ell × Fin ell) ℂ) V
    D.conjTranspose * Q * D =
      fun x y => (V.conjTranspose *
        Matrix.kronecker (block A x.1.1 y.1.1) (block B x.1.2 y.1.2) * V) x.2 y.2 := by
  classical
  dsimp only
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.prodProdProdComm_symm, Equiv.prodProdProdComm_apply, block, Matrix.one_apply,
    Prod.fst, Prod.snd, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul,
    apply_ite, star_one, star_zero]
  simp [eq_comm, Finset.sum_ite_eq', Finset.sum_ite_eq]

private theorem kraus_jcp {n m N : ℕ} {Phi : MatrixProduct n m}
    (h : HasKrausRepresentation Phi N) : IsJointlyCompletelyPositive Phi := by
  classical
  obtain ⟨V, hV⟩ := h
  intro ell _ A B hA hB
  let Q : Matrix ((Fin ell × Fin ell) × Input n) ((Fin ell × Fin ell) × Input n) ℂ :=
    Matrix.reindex (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)
      (Matrix.kronecker A B)
  let D (k : Fin N) : Matrix ((Fin ell × Fin ell) × Input n) ((Fin ell × Fin ell) × Fin m) ℂ :=
    Matrix.kronecker (1 : Matrix (Fin ell × Fin ell) (Fin ell × Fin ell) ℂ) (V k)
  have hQ : Q.PosSemidef := (hA.kronecker hB).submatrix _
  have hsum : (∑ k, (D k).conjTranspose * Q * D k).PosSemidef :=
    Matrix.posSemidef_sum fun k _ => hQ.conjTranspose_mul_mul_same (D k)
  convert hsum using 1
  ext x y
  simp only [jointAmplification, hV, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun k _ =>
    (congrArg (fun M : Matrix _ _ ℂ => M x y) (sandwich_entries A B (V k))).symm

private theorem choi_rank_le_length {n m N : ℕ} {Phi : MatrixProduct n m}
    (h : HasKrausRepresentation Phi N) : (choiMatrix Phi).rank ≤ N := by
  classical
  obtain ⟨V, hV⟩ := h
  let K (k : Fin N) := (V k).conjTranspose
  let W : Matrix (D5Index n m) (Fin N) ℂ := fun x k => K k x.1 x.2
  have hC : d5Choi Phi = W * W.conjTranspose := by
    rw [← d5Choi_linearization, linearization_eq_kraus V hV, MatrixMap.choi_of_kraus]
    ext x y
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.vecMulVec, W, K]
  have hr : (d5Choi Phi).rank = (choiMatrix Phi).rank := Matrix.rank_reindex _ _ _
  rw [← hr, hC]
  exact (Matrix.rank_mul_le_left _ _).trans W.rank_le_width

private theorem card_cube (n : ℕ) : Fintype.card (D5Index n n) = n ^ 3 := by
  simp [D5Index, Input, pow_succ, Nat.mul_assoc]

private theorem choiKrausRank_le_of_psd {n : ℕ} {Phi : MatrixProduct n n}
    (h : (choiMatrix Phi).PosSemidef) : choiKrausRank Phi ≤ ((n ^ 3 : ℕ) : ℕ∞) := by
  apply sInf_le
  exact ⟨n ^ 3, rfl, card_cube n ▸ psd_has_kraus h⟩

/-- A positive-definite Choi matrix yields joint positivity at every block size
and forces the minimum Kraus length to be the full Choi dimension. -/
private theorem posDef_checkpoint {n : ℕ} {Phi : MatrixProduct n n}
    (h : (choiMatrix Phi).PosDef) :
    IsJointlyCompletelyPositive Phi ∧ choiKrausRank Phi = ((n ^ 3 : ℕ) : ℕ∞) := by
  have hRank : (choiMatrix Phi).rank = n ^ 3 := by
    rw [Matrix.rank_of_isUnit _ h.isUnit]
    simp [pow_succ, Nat.mul_assoc]
  refine ⟨kraus_jcp (psd_has_kraus h.posSemidef),
    le_antisymm (choiKrausRank_le_of_psd h.posSemidef) ?_⟩
  apply le_sInf
  rintro _ ⟨N, rfl, hN⟩
  exact_mod_cast (hRank ▸ choi_rank_le_length hN)

end

end D5.S3.Quantum.Foundation.EvertJuryMcCulloughMaxChoiKrausRank
