/- GID: D5/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/EvertJuryMcCulloughMaxChoiKrausRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp Kraus length bounds for jointly completely positive products with units. -/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Module
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation

/-!
# Maximum Choi–Kraus rank of a matrix product with a unit

Question 1 of Eric Evert, Michael T. Jury and Scott McCullough,
*Completely Positive Matrix Products*, arXiv:2607.13251v1.
The attaining product adds a positive-definite Choi contribution to a weighted
Schur product while preserving its common unit.
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
  simp only [Matrix.single_apply, ite_and, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

private theorem linearization_kronecker {n m : ℕ} (Phi : MatrixProduct n m)
    (A B : CMatrix n) : linearization Phi (Matrix.kronecker A B) = Phi A B := by
  let F : MatrixProduct n m :=
    (LinearMap.compRight ℂ (linearization Phi)).comp (Matrix.kroneckerBilinear (R := ℂ) (α := ℂ))
  have hF : F = Phi := by
    apply (Matrix.stdBasis ℂ (Fin n) (Fin n)).ext
    rintro ⟨i, j⟩
    apply (Matrix.stdBasis ℂ (Fin n) (Fin n)).ext
    rintro ⟨s, t⟩
    simp only [Matrix.stdBasis_eq_single]
    change linearization Phi (Matrix.kronecker (single i j 1) (single s t 1)) = _
    rw [Matrix.kronecker, Matrix.single_kronecker_single, one_mul, linearization_single]
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
  rw [Matrix.stdBasis_eq_single, linearization_single, hV, Matrix.kronecker,
    Matrix.single_kronecker_single, one_mul]
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

private abbrev Blocks (ell : ℕ) := Fin ell × Fin ell

private def amplificationInput {n ell : ℕ}
    (A B : Matrix (Fin ell × Fin n) (Fin ell × Fin n) ℂ) :
    Matrix (Blocks ell × Input n) (Blocks ell × Input n) ℂ :=
  Matrix.reindex (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)
    (Matrix.kronecker A B)

private def amplificationCoeff {n m ell : ℕ} (V : Matrix (Input n) (Fin m) ℂ) :
    Matrix (Blocks ell × Input n) (Blocks ell × Fin m) ℂ :=
  Matrix.kronecker (1 : Matrix (Blocks ell) (Blocks ell) ℂ) V

private theorem sandwich_entries {n m ell : ℕ}
    (A B : Matrix (Fin ell × Fin n) (Fin ell × Fin n) ℂ)
    (V : Matrix (Input n) (Fin m) ℂ) :
    (amplificationCoeff (ell := ell) V).conjTranspose * amplificationInput A B *
      amplificationCoeff V =
      fun x y => (V.conjTranspose *
        Matrix.kronecker (block A x.1.1 y.1.1) (block B x.1.2 y.1.2) * V) x.2 y.2 := by
  classical
  let D := amplificationCoeff (ell := ell) V
  let Q := amplificationInput A B
  let blockKron (x y : Blocks ell) :=
    Matrix.kronecker (block A x.1 y.1) (block B x.2 y.2)
  have hD (x y : Blocks ell) (u : Input n) (a : Fin m) :
      D (x, u) (y, a) = if x = y then V u a else 0 := by
    change (1 : Matrix (Blocks ell) (Blocks ell) ℂ) x y * V u a = _
    simp [Matrix.one_apply, ite_mul]
  have hQ (x y : Blocks ell) (u v : Input n) :
      Q (x,u) (y,v) = blockKron x y u v := rfl
  have hleft (x y : Blocks ell) (a : Fin m) (v : Input n) :
      (D.conjTranspose * Q) (x, a) (y, v) = (V.conjTranspose * blockKron x y) a v := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single x]
    · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hD, hQ]
    · intro z _ hz
      simp [Matrix.conjTranspose_apply, hD, hz]
    · simp
  ext ⟨x, a⟩ ⟨y, b⟩
  change (D.conjTranspose * Q * D) (x, a) (y, b) =
    (V.conjTranspose * blockKron x y * V) a b
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single y]
  · simp [Matrix.mul_apply, hleft, hD]
  · intro z _ hz
    simp [hD, hz]
  · simp

private theorem kraus_jcp {n m N : ℕ} {Phi : MatrixProduct n m}
    (h : HasKrausRepresentation Phi N) : IsJointlyCompletelyPositive Phi := by
  classical
  obtain ⟨V, hV⟩ := h
  intro ell _ A B hA hB
  let Q := amplificationInput A B
  let D := fun k => amplificationCoeff (ell := ell) (V k)
  have hQ : Q.PosSemidef := (hA.kronecker hB).submatrix _
  have hsum : (∑ k, (D k).conjTranspose * Q * D k).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun k _ => hQ.conjTranspose_mul_mul_same (D k)
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
    change (∑ k, Matrix.vecMulVec (fun z : D5Index n m => K k z.1 z.2)
      (fun z : D5Index n m => star (K k z.1 z.2))) x y = (W * W.conjTranspose) x y
    rw [Matrix.sum_apply, Matrix.mul_apply]
    rfl
  have hr : (d5Choi Phi).rank = (choiMatrix Phi).rank := Matrix.rank_reindex _ _ _
  rw [← hr, hC]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using W.rank_le_card_width)

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


open scoped Kronecker

private def allOnes (n : ℕ) : CMatrix n := fun _ _ => 1

private theorem allOnes_mul (n : ℕ) : allOnes n * allOnes n = (n : ℂ) • allOnes n := by
  ext i j
  simp [Matrix.mul_apply, allOnes]

private theorem allOnes_psd (n : ℕ) : (allOnes n).PosSemidef := by
  convert Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin n => (1 : ℂ)) using 1
  ext i j
  simp [allOnes, Matrix.vecMulVec]

private def weight (n : ℕ) : CMatrix n := 1 + allOnes n

private def commonUnit (n : ℕ) : CMatrix n := allOnes n - (1 / 2 : ℂ) • (1 : CMatrix n)

private def traceWeight (n : ℕ) : CMatrix n :=
  (2 * (n : ℂ) - 1) • (1 : CMatrix n) - allOnes n

private def traceFunctional (n : ℕ) : CMatrix n →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (n := Fin n) ℂ ℂ).comp
    (LinearMap.mul ℂ (CMatrix n) (traceWeight n))

private theorem traceFunctional_apply (n : ℕ) (A : CMatrix n) :
    traceFunctional n A = (traceWeight n * A).trace := rfl

private theorem traceFunctional_commonUnit (n : ℕ) : traceFunctional n (commonUnit n) = 0 := by
  rw [traceFunctional_apply]
  have h : traceWeight n * commonUnit n =
      ((n : ℂ) - 1 / 2) • (allOnes n - (1 : CMatrix n)) := by
    simp only [traceWeight, commonUnit, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, allOnes_mul]
    module
  rw [h, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one]
  simp [Matrix.trace, allOnes]

private theorem traceWeight_posDef (n : ℕ) (hn : 2 ≤ n) : (traceWeight n).PosDef := by
  let K : CMatrix n := (n : ℂ) • (1 : CMatrix n) - allOnes n
  have hKstar : K.conjTranspose = K := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [K, Matrix.conjTranspose_apply, Matrix.one_apply_eq, allOnes]
    · simp [K, Matrix.conjTranspose_apply, Matrix.one_apply_ne, h, Ne.symm h, allOnes]
  have hKsq : K * K = (n : ℂ) • K := by
    simp only [K, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, allOnes_mul]
    module
  have hK : K.PosSemidef := by
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hnonneg : (0 : ℂ) ≤ (n : ℂ)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
      exact Complex.zero_le_real.mpr (by positivity)
    have hGram := (Matrix.posSemidef_conjTranspose_mul_self K).smul hnonneg
    rw [hKstar, hKsq, smul_smul, inv_mul_cancel₀ hn0, one_smul] at hGram
    exact hGram
  have hpos : (0 : ℂ) < (n : ℂ) - 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.zero_lt_real]
    have hreal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hh : traceWeight n = ((n : ℂ) - 1) • (1 : CMatrix n) + K := by
    simp only [traceWeight, K]
    module
  rw [hh]
  exact (Matrix.PosDef.one.smul hpos).add_posSemidef hK

private def weightedValue (n : ℕ) (A B : CMatrix n) : CMatrix n :=
  fun i j => weight n i j * A i j * B i j +
    traceFunctional n A * traceFunctional n B * (1 : CMatrix n) i j

/-- The weighted Schur product plus the trace perturbation. -/
private def weightedProduct (n : ℕ) : MatrixProduct n n where
  toFun A := {
    toFun := weightedValue n A
    map_add' B C := by
      ext i j
      change weightedValue n A (B + C) i j =
        weightedValue n A B i j + weightedValue n A C i j
      simp only [weightedValue, Matrix.add_apply, map_add]
      ring
    map_smul' c B := by
      ext i j
      change weightedValue n A (c • B) i j = c * weightedValue n A B i j
      simp only [weightedValue, Matrix.smul_apply, map_smul, smul_eq_mul]
      ring }
  map_add' A B := by
    apply LinearMap.ext
    intro C
    ext i j
    change weightedValue n (A + B) C i j =
      weightedValue n A C i j + weightedValue n B C i j
    simp only [weightedValue, Matrix.add_apply, map_add]
    ring
  map_smul' c A := by
    apply LinearMap.ext
    intro B
    ext i j
    change weightedValue n (c • A) B i j = c * weightedValue n A B i j
    simp only [weightedValue, Matrix.smul_apply, map_smul, smul_eq_mul]
    ring

private theorem weightedProduct_apply (n : ℕ) (A B : CMatrix n) (i j : Fin n) :
    weightedProduct n A B i j = weight n i j * A i j * B i j +
      traceFunctional n A * traceFunctional n B * (1 : CMatrix n) i j := rfl

private theorem weightedProduct_commonUnit (n : ℕ) : IsUnit (weightedProduct n) (commonUnit n) := by
  have hweight (i j : Fin n) : weight n i j * commonUnit n i j = 1 := by
    by_cases hij : i = j
    · subst j
      norm_num [weight, commonUnit, allOnes]
    · simp [weight, commonUnit, allOnes, Matrix.one_apply_ne hij]
  constructor
  · intro B
    ext i j
    rw [weightedProduct_apply, traceFunctional_commonUnit, hweight]
    simp
  · intro A
    ext i j
    rw [weightedProduct_apply, traceFunctional_commonUnit, mul_right_comm, hweight]
    simp

private def diagonalEmbedding (n : ℕ) : Matrix (Fin n) (SourceIndex n n) ℂ :=
  fun a x => if x.1.1 = x.2 ∧ x.1.2 = x.2 ∧ a = x.2 then 1 else 0

private theorem weightedProduct_choi (n : ℕ) :
    choiMatrix (weightedProduct n) =
      (diagonalEmbedding n).conjTranspose * weight n * diagonalEmbedding n +
      ((traceWeight n).transpose ⊗ₖ (traceWeight n).transpose) ⊗ₖ (1 : CMatrix n) := by
  ext ⟨⟨i, s⟩, a⟩ ⟨⟨j, t⟩, b⟩
  simp only [choiMatrix, weightedProduct_apply, traceFunctional_apply, Matrix.trace_mul_single,
    MulOpposite.op_one, one_smul, Matrix.add_apply, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply]
  congr 1
  by_cases hi : i = a <;> by_cases hs : s = a <;> by_cases hj : j = b <;> by_cases ht : t = b <;>
    simp [diagonalEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply, hi, hs, hj, ht]

private theorem weightedProduct_choi_posDef (n : ℕ) (hn : 2 ≤ n) :
    (choiMatrix (weightedProduct n)).PosDef := by
  have hP : (weight n).PosSemidef := Matrix.PosSemidef.one.add (allOnes_psd n)
  have hH := (traceWeight_posDef n hn).transpose
  rw [weightedProduct_choi, add_comm]
  exact ((hH.kronecker hH).kronecker Matrix.PosDef.one).add_posSemidef
    (hP.conjTranspose_mul_mul_same (diagonalEmbedding n))

private def scalarProduct : MatrixProduct 1 1 := LinearMap.mul ℂ (CMatrix 1)

private theorem scalarProduct_unit : IsUnit scalarProduct 1 :=
  ⟨fun A => one_mul A, fun A => mul_one A⟩

private theorem scalarProduct_choi_posDef : (choiMatrix scalarProduct).PosDef := by
  have hC : choiMatrix scalarProduct = 1 := by
    ext x y
    have hx : x = ((0, 0), 0) := Subsingleton.elim _ _
    have hy : y = ((0, 0), 0) := Subsingleton.elim _ _
    subst x
    subst y
    simp [choiMatrix, scalarProduct, Matrix.mul_apply]
  rw [hC]
  exact Matrix.PosDef.one

private theorem attaining_product (n : ℕ) (hn : 1 ≤ n) :
    ∃ Phi : MatrixProduct n n, IsJointlyCompletelyPositive Phi ∧
      (∃ T : CMatrix n, IsUnit Phi T) ∧ choiKrausRank Phi = ((n ^ 3 : ℕ) : ℕ∞) := by
  by_cases h : n = 1
  · subst n
    obtain ⟨hJ, hR⟩ := posDef_checkpoint scalarProduct_choi_posDef
    exact ⟨scalarProduct, hJ, ⟨1, scalarProduct_unit⟩, hR⟩
  · obtain ⟨hJ, hR⟩ := posDef_checkpoint (weightedProduct_choi_posDef n (by omega))
    exact ⟨weightedProduct n, hJ, ⟨commonUnit n, weightedProduct_commonUnit n⟩, hR⟩

/-- Both unit classes have maximum Choi–Kraus rank n³ in every positive dimension. -/
theorem result : claim := by
  intro n hn
  obtain ⟨Phi, hJ, ⟨T, hT⟩, hR⟩ := attaining_product n hn
  have hUpper (Psi : MatrixProduct n n) (hPsi : IsJointlyCompletelyPositive Psi) :
      choiKrausRank Psi ≤ ((n ^ 3 : ℕ) : ℕ∞) :=
    choiKrausRank_le_of_psd (jcp_choi_psd hn hPsi)
  exact ⟨⟨fun Psi hPsi _ => hUpper Psi hPsi, ⟨Phi, hJ, ⟨T, hT.1⟩, hR⟩⟩,
    ⟨fun Psi hPsi _ => hUpper Psi hPsi, ⟨Phi, hJ, ⟨T, hT⟩, hR⟩⟩⟩

end

end D5.S3.Quantum.Foundation.EvertJuryMcCulloughMaxChoiKrausRank
