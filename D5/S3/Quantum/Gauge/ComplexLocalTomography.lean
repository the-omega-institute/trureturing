/- GID: D5/S3/Quantum/Gauge/ComplexLocalTomography
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/ComplexLocalTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Self-adjoint bases and tomography over the three real division algebras. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
A self-adjoint matrix is specified by its real diagonal and the entries strictly
above it. For complex scalars the local bases give a basis of the composite by
Kronecker product. For real scalars a tensor of two skew matrices gives a
nonzero self-adjoint direction invisible to all symmetric local products.
-/
compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped Kronecker Quaternion

noncomputable section

namespace D5.S3.Quantum.Gauge.ComplexLocalTomography

abbrev Hermitian (ι A : Type*) [AddGroup A] [StarAddMonoid A] :=
  selfAdjoint (Matrix ι ι A)

abbrev Upper (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev HermitianIndex (n : ℕ) (ι : Type*) := Fin n ⊕ (Upper n × ι)

private def upperCoordinates {A : Type*} [AddCommGroup A] [StarAddMonoid A]
    [Module ℝ A] [StarModule ℝ A] (n : ℕ)
    (e : selfAdjoint A ≃ₗ[ℝ] ℝ) :
    Hermitian (Fin n) A ≃ₗ[ℝ] (Fin n → ℝ) × (Upper n → A) := by
  let entry (M : Hermitian (Fin n) A) (i j : Fin n) : A := M.val i j
  have symmEntry (M : Hermitian (Fin n) A) (i j : Fin n) :
      star (entry M j i) = entry M i j := congrFun₂ M.property i j
  let diag (M : Hermitian (Fin n) A) (i : Fin n) : selfAdjoint A :=
    ⟨entry M i i, symmEntry M i i⟩
  let assemble (x : (Fin n → ℝ) × (Upper n → A)) : Matrix (Fin n) (Fin n) A :=
    fun i j => if h : i < j then x.2 ⟨(i, j), h⟩
    else if h' : j < i then star (x.2 ⟨(j, i), h'⟩)
    else (e.symm (x.1 i)).val
  have assembledHermitian (x) : Matrix.IsHermitian (assemble x) := by
    apply Matrix.ext
    intro i j
    change star (assemble x j i) = assemble x i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [assemble, hij, not_lt_of_gt hij]
    · simp [assemble]
    · simp [assemble, hji, not_lt_of_gt hji]
  refine
    { toFun := fun M => (fun i => e (diag M i), fun p => entry M p.val.1 p.val.2)
      invFun := fun x => ⟨assemble x, assembledHermitian x⟩
      left_inv := ?left
      right_inv := ?right
      map_add' := ?add
      map_smul' := ?smul }
  case left =>
    intro M
    apply Subtype.ext
    ext i j
    change assemble (fun i => e (diag M i), fun p => entry M p.val.1 p.val.2) i j = _
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [assemble, hij, entry]
    · simp [assemble, entry, diag]
    · simpa [assemble, hji, not_lt_of_gt hji] using symmEntry M i j
  case right =>
    intro x
    apply Prod.ext
    · funext i
      change e (diag ⟨assemble x, assembledHermitian x⟩ i) = x.1 i
      calc
        _ = e (e.symm (x.1 i)) := by
          congr 1
          apply Subtype.ext
          change assemble x i i = (e.symm (x.1 i)).val
          simp [assemble]
        _ = _ := e.apply_symm_apply _
    · funext p
      change assemble x p.val.1 p.val.2 = x.2 p
      simp [assemble, p.property]
  case add =>
    intro M N
    apply Prod.ext
    · funext i
      exact e.map_add (diag M i) (diag N i)
    · rfl
  case smul =>
    intro r M
    apply Prod.ext
    · funext i
      exact e.map_smul r (diag M i)
    · rfl

private def realDiagonal : selfAdjoint ℝ ≃ₗ[ℝ] ℝ where
  toFun x := x.val
  invFun x := ⟨x, star_trivial x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance quaternionRealStarModule : StarModule ℝ ℍ[ℝ] where
  star_smul r a := by rw [Quaternion.star_smul, star_trivial r]

private def quaternionDiagonal : selfAdjoint ℍ[ℝ] ≃ₗ[ℝ] ℝ where
  toFun x := x.val.re
  invFun x := ⟨↑x, Quaternion.star_coe x⟩
  left_inv x := Subtype.ext ((Quaternion.star_eq_self.mp x.property).symm)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The diagonal units and the upper-entry units paired with their adjoints. -/
private def coordinateBasis {A ι : Type*} [AddCommGroup A] [StarAddMonoid A]
    [Module ℝ A] [StarModule ℝ A] (n : ℕ) [Fintype ι]
    (diag : selfAdjoint A ≃ₗ[ℝ] ℝ) (scalar : Module.Basis ι ℝ A) :
    Module.Basis (HermitianIndex n ι) ℝ (Hermitian (Fin n) A) :=
  ((Pi.basisFun ℝ (Fin n)).prod
    ((Pi.basis fun _ : Upper n => scalar).reindex (Equiv.sigmaEquivProd _ _))).map
      (upperCoordinates n diag).symm

/-- The real symmetric basis uses one unit per diagonal or unordered off-diagonal pair. -/
def realSymBasis (n : ℕ) : Module.Basis (HermitianIndex n Unit) ℝ (Hermitian (Fin n) ℝ) :=
  coordinateBasis n realDiagonal (Module.Basis.singleton Unit ℝ)

/-- The complex Hermitian basis uses the scalar basis 1, I above the diagonal. -/
def complexHermBasis (n : ℕ) :
    Module.Basis (HermitianIndex n (Fin 2)) ℝ (Hermitian (Fin n) ℂ) :=
  coordinateBasis n Complex.selfAdjointEquiv Complex.basisOneI

/-- The quaternionic Hermitian basis uses the scalar basis 1, I, J, K above the diagonal. -/
def quaternionHermBasis (n : ℕ) :
    Module.Basis (HermitianIndex n (Fin 4)) ℝ (Hermitian (Fin n) ℍ[ℝ]) :=
  coordinateBasis n quaternionDiagonal (QuaternionAlgebra.basisOneIJK (-1) 0 (-1))

private theorem card_upper (n : ℕ) : Fintype.card (Upper n) = n.choose 2 := by
  rw [Fintype.card_subtype]
  simpa [Finset.univ_product_univ] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n))))

private theorem twice_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right, mul_comm 2, Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd]

private theorem twice_real_dimension (n : ℕ) : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
  rw [mul_comm 2, Nat.div_mul_cancel (Nat.even_mul_succ_self n).two_dvd]

theorem finrank_realHermitian (n : ℕ) :
    Module.finrank ℝ (Hermitian (Fin n) ℝ) = n * (n + 1) / 2 := by
  rw [Module.finrank_eq_card_basis (realSymBasis n)]
  simp only [HermitianIndex, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, card_upper,
    Fintype.card_unit, mul_one]
  have h := twice_choose_two n
  have hr := twice_real_dimension n
  cases n with
  | zero => decide
  | succ n =>
    simp only [Nat.succ_sub_one] at h
    nlinarith

theorem finrank_complexHermitian (n : ℕ) :
    Module.finrank ℝ (Hermitian (Fin n) ℂ) = n ^ 2 := by
  rw [Module.finrank_eq_card_basis (complexHermBasis n)]
  simp only [HermitianIndex, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, card_upper]
  have h := twice_choose_two n
  cases n with
  | zero => decide
  | succ n =>
    simp only [Nat.succ_sub_one] at h
    nlinarith

theorem finrank_quaternionHermitian (n : ℕ) :
    Module.finrank ℝ (Hermitian (Fin n) ℍ[ℝ]) = n * (2 * n - 1) := by
  rw [Module.finrank_eq_card_basis (quaternionHermBasis n)]
  simp only [HermitianIndex, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, card_upper]
  have h := twice_choose_two n
  cases n with
  | zero => decide
  | succ n =>
    simp only [Nat.succ_sub_one] at h
    have hsub : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    rw [hsub]
    nlinarith

private theorem real_excess (m k : ℕ) (hm : 2 ≤ m) (hk : 2 ≤ k) :
    m * (m + 1) / 2 * (k * (k + 1) / 2) < m * k * (m * k + 1) / 2 := by
  let r (n : ℕ) := n * (n + 1) / 2
  change r m * r k < r (m * k)
  have hr (n : ℕ) : 2 * r n = n * (n + 1) := twice_real_dimension n
  have hpos : 0 < m * k * (m - 1) * (k - 1) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
  have hdiff : 4 * r (m * k) =
      4 * (r m * r k) + m * k * (m - 1) * (k - 1) := by
    calc
      _ = 2 * (2 * r (m * k)) := by ring
      _ = 2 * (m * k * (m * k + 1)) := by rw [hr]
      _ = (m * (m + 1)) * (k * (k + 1)) + m * k * (m - 1) * (k - 1) := by
        obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ m by omega)
        obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ k by omega)
        simp only [Nat.add_comm 1, Nat.add_sub_cancel]
        ring
      _ = _ := by rw [← hr m, ← hr k]; ring
  omega

private theorem quaternion_deficit (m k : ℕ) (hm : 2 ≤ m) (hk : 2 ≤ k) :
    m * k * (2 * (m * k) - 1) < m * (2 * m - 1) * (k * (2 * k - 1)) := by
  have hm' : 1 ≤ m := by omega
  have hk' : 1 ≤ k := by omega
  have hmk : 1 ≤ m * k := Nat.mul_pos hm' hk'
  have hpos : 0 < 2 * m * k * (m - 1) * (k - 1) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hm') hk') (by omega)) (by omega)
  have hdiff : m * (2 * m - 1) * (k * (2 * k - 1)) =
      m * k * (2 * (m * k) - 1) + 2 * m * k * (m - 1) * (k - 1) := by
    have h₂m : 1 ≤ 2 * m := by omega
    have h₂k : 1 ≤ 2 * k := by omega
    have h₂mk : 1 ≤ 2 * (m * k) := by omega
    zify [hm', hk', h₂m, h₂k, h₂mk]
    ring
  omega

/-- For two nontrivial local systems, dimension multiplicativity selects the complex case. -/
theorem division_algebra_local_tomography_selection (m k : ℕ) (hm : 2 ≤ m) (hk : 2 ≤ k) :
    Module.finrank ℝ (Hermitian (Fin m) ℝ) * Module.finrank ℝ (Hermitian (Fin k) ℝ) <
      Module.finrank ℝ (Hermitian (Fin (m * k)) ℝ) ∧
    Module.finrank ℝ (Hermitian (Fin (m * k)) ℂ) =
      Module.finrank ℝ (Hermitian (Fin m) ℂ) * Module.finrank ℝ (Hermitian (Fin k) ℂ) ∧
    Module.finrank ℝ (Hermitian (Fin (m * k)) ℍ[ℝ]) <
      Module.finrank ℝ (Hermitian (Fin m) ℍ[ℝ]) * Module.finrank ℝ (Hermitian (Fin k) ℍ[ℝ]) := by
  simp only [finrank_realHermitian, finrank_complexHermitian, finrank_quaternionHermitian]
  exact ⟨real_excess m k hm hk, mul_pow m k 2, quaternion_deficit m k hm hk⟩

private abbrev CIndex (n : ℕ) := HermitianIndex n (Fin 2)
private abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
private abbrev Composite (m k : ℕ) := Hermitian (Fin m × Fin k) ℂ

private theorem complex_basis_spans_matrices (n : ℕ) :
    Submodule.span ℂ (Set.range (fun i => (complexHermBasis n i).val)) =
      (⊤ : Submodule ℂ (CMat n)) := by
  rw [← span_selfAdjoint]
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact (complexHermBasis n i).property)
  · apply Submodule.span_le.mpr
    intro A hA
    let X : Hermitian (Fin n) ℂ := ⟨A, hA⟩
    let f : Hermitian (Fin n) ℂ →ₗ[ℝ] CMat n :=
      { toFun := Subtype.val
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hsum := congrArg f ((complexHermBasis n).sum_repr X)
    rw [map_sum f] at hsum
    change (∑ i, f (((complexHermBasis n).repr X i) • complexHermBasis n i)) = A at hsum
    rw [← hsum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul, ← Complex.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The product of two Hermitian matrices on distinct factors. -/
def productObservable {m k : ℕ} (A : Hermitian (Fin m) ℂ) (B : Hermitian (Fin k) ℂ) :
    Hermitian (Fin m × Fin k) ℂ :=
  ⟨A.val ⊗ₖ B.val, by
    change (A.val ⊗ₖ B.val)ᴴ = _
    rw [Matrix.conjTranspose_kronecker, show A.valᴴ = A.val from A.property,
      show B.valᴴ = B.val from B.property]⟩

private def productBasisVector (m k : ℕ) (p : CIndex m × CIndex k) : Composite m k :=
  productObservable (complexHermBasis m p.1) (complexHermBasis k p.2)

private theorem productBasis_spans_matrices (m k : ℕ) :
    Submodule.span ℂ (Set.range (fun p => (productBasisVector m k p).val)) = ⊤ := by
  let V := Submodule.span ℂ (Set.range (fun p => (productBasisVector m k p).val))
  let K : CMat m →ₗ[ℂ] CMat k →ₗ[ℂ] Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ :=
    Matrix.kroneckerBilinear
  have right_mem (i : CIndex m) (B : CMat k) : K (complexHermBasis m i).val B ∈ V := by
    change B ∈ V.comap (K (complexHermBasis m i).val)
    have hle : ⊤ ≤ V.comap (K (complexHermBasis m i).val) := by
      rw [← complex_basis_spans_matrices k, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(i, j), rfl⟩
    exact hle Submodule.mem_top
  have both_mem (A : CMat m) (B : CMat k) : K A B ∈ V := by
    let f := (LinearMap.applyₗ (R := ℂ) B).comp K
    change A ∈ V.comap f
    have hle : ⊤ ≤ V.comap f := by
      rw [← complex_basis_spans_matrices m, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact right_mem i B
    exact hle Submodule.mem_top
  change V = ⊤
  rw [eq_top_iff, ← (Matrix.stdBasis ℂ (Fin m × Fin k) (Fin m × Fin k)).span_eq,
    Submodule.span_le]
  rintro _ ⟨⟨⟨i, a⟩, ⟨j, b⟩⟩, rfl⟩
  rw [Matrix.stdBasis_eq_single]
  change Matrix.single (i, a) (j, b) 1 ∈ V
  have hp := both_mem (Matrix.single i j 1) (Matrix.single a b 1)
  change ((Matrix.single i j (1 : ℂ)) ⊗ₖ Matrix.single a b 1) ∈ V at hp
  simpa only [Matrix.single_kronecker_single, one_mul] using hp

private def compositeReindex (m k : ℕ) : Composite m k ≃ₗ[ℝ] Hermitian (Fin (m * k)) ℂ := by
  let e : Fin m × Fin k ≃ Fin (m * k) := finProdFinEquiv
  let f := Matrix.reindexLinearEquiv ℝ ℂ e e
  have symmHerm (A : Hermitian (Fin (m * k)) ℂ) : (f.symm A.val).IsHermitian := by
    change ((Matrix.reindexLinearEquiv ℝ ℂ e e).symm A.val).IsHermitian
    rw [Matrix.symm_reindexLinearEquiv]
    exact Matrix.IsHermitian.reindex A.property e.symm
  refine
    { toFun := fun A => ⟨f A.val, Matrix.IsHermitian.reindex A.property e⟩
      invFun := fun A => ⟨f.symm A.val, symmHerm A⟩
      left_inv := fun A => Subtype.ext (f.symm_apply_apply A.val)
      right_inv := fun A => Subtype.ext (f.apply_symm_apply A.val)
      map_add' := fun A B => Subtype.ext (f.map_add A.val B.val)
      map_smul' := fun r A => Subtype.ext (f.map_smul r A.val) }

private theorem card_CIndex (n : ℕ) : Fintype.card (CIndex n) = n ^ 2 :=
  (Module.finrank_eq_card_basis (complexHermBasis n)).symm.trans (finrank_complexHermitian n)

private theorem productBasis_independent (m k : ℕ) :
    LinearIndependent ℝ (productBasisVector m k) := by
  have hc : LinearIndependent ℂ (fun p => (productBasisVector m k p).val) := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · exact (productBasis_spans_matrices m k).ge
    · rw [Fintype.card_prod, card_CIndex, card_CIndex, Module.finrank_matrix]
      simp only [Fintype.card_prod, Fintype.card_fin, Module.finrank_self, mul_one]
      ring
  let f : Composite m k →ₗ[ℝ] Matrix (Fin m × Fin k) (Fin m × Fin k) ℂ :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (hc.restrict_scalars' ℝ).of_comp f

/-- The explicit tensor-product basis consists of all pairs of local Hermitian basis elements. -/
def tensorHermBasis (m k : ℕ) :
    Module.Basis (HermitianIndex m (Fin 2) × HermitianIndex k (Fin 2)) ℝ
      (Hermitian (Fin m × Fin k) ℂ) :=
  Module.Basis.mk (productBasis_independent m k) (by
    have h : Module.finrank ℝ (Composite m k) = (m * k) ^ 2 :=
      (compositeReindex m k).finrank_eq.trans
        (D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition.hermitian_space_finrank (m * k))
    let : FiniteDimensional ℝ (Hermitian (Fin (m * k)) ℂ) :=
      Module.Finite.of_basis (complexHermBasis (m * k))
    let : FiniteDimensional ℝ (Composite m k) :=
      FiniteDimensional.of_injective (compositeReindex m k).toLinearMap
        (compositeReindex m k).injective
    apply (Submodule.eq_top_of_finrank_eq _).ge
    rw [finrank_span_eq_card (productBasis_independent m k), h, Fintype.card_prod,
      card_CIndex, card_CIndex, mul_pow])

theorem tensorHermBasis_apply (m k : ℕ) (i : HermitianIndex m (Fin 2))
    (j : HermitianIndex k (Fin 2)) :
    tensorHermBasis m k (i, j) = productObservable (complexHermBasis m i) (complexHermBasis k j) := by
  simp [tensorHermBasis, productBasisVector]

theorem span_tensor_hermitian (m k : ℕ) :
    Submodule.span ℝ
      (Set.range (fun p : Hermitian (Fin m) ℂ × Hermitian (Fin k) ℂ =>
        productObservable p.1 p.2)) = (⊤ : Submodule ℝ (Hermitian (Fin m × Fin k) ℂ)) := by
  apply top_unique
  rw [← (tensorHermBasis m k).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨⟨i, j⟩, rfl⟩
  exact ⟨(complexHermBasis m i, complexHermBasis k j),
    (tensorHermBasis_apply m k i j).symm⟩

/-- The canonical skew matrix on the two real coordinates. -/
def J₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

private theorem transpose_J₂ : J₂ᵀ = -J₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J₂]

/-- The tensor of two skew directions is a symmetric direction on the composite. -/
def W : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := J₂ ⊗ₖ J₂

theorem W_symmetric : W.IsSymm := by
  change Wᵀ = W
  rw [W, show (J₂ ⊗ₖ J₂)ᵀ = J₂ᵀ ⊗ₖ J₂ᵀ from Matrix.kroneckerMap_transpose _ _ _,
    transpose_J₂]
  ext i j
  simp

private theorem trace_mul_J₂ (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.IsSymm) :
    (A * J₂).trace = 0 := by
  have h : (A * J₂).trace = -(A * J₂).trace := calc
    _ = ((A * J₂)ᵀ).trace := (Matrix.trace_transpose _).symm
    _ = -(A * J₂).trace := by
      rw [Matrix.transpose_mul, transpose_J₂, hA.eq, Matrix.neg_mul, Matrix.trace_neg,
        Matrix.trace_mul_comm J₂ A]
  linarith

theorem blind_spot_trace (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.IsSymm) (hB : B.IsSymm) : ((A ⊗ₖ B) * W).trace = 0 := by
  rw [W, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker,
    trace_mul_J₂ A hA, trace_mul_J₂ B hB, zero_mul]

private def quarterMix (t : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  (1 / 4 : ℝ) • 1 + t • W

def rhoPlus : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := quarterMix (1 / 16)
def rhoMinus : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := quarterMix (-(1 / 16))

private theorem quarterMix_trace (t : ℝ) : (quarterMix t).trace = 1 := by
  have hJ : J₂.trace = 0 := by norm_num [Matrix.trace, Fin.sum_univ_two, J₂]
  norm_num [quarterMix, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, W,
    Matrix.trace_kronecker, hJ]

private theorem quarterMix_posDef (t : ℝ) (ht : |t| < 1 / 4) : (quarterMix t).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · change (quarterMix t)ᴴ = _
    rw [quarterMix, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.conjTranspose_eq_transpose_of_trivial, W_symmetric.eq]
    simp
  · intro x hx
    let a := x (0, 0)
    let b := x (0, 1)
    let c := x (1, 0)
    let d := x (1, 1)
    have hform : star x ⬝ᵥ (quarterMix t *ᵥ x) =
        (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 4 + t * (2 * (a * d - b * c)) := by
      norm_num [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
        quarterMix, W, Matrix.kronecker_apply, J₂, Matrix.one_apply, a, b, c, d]
      ring
    rw [hform]
    have hs : 0 < a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
      have hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0 := by
        by_contra! he
        apply hx
        funext i
        obtain ⟨i, j⟩ := i
        fin_cases i <;> fin_cases j
        · exact he.1
        · exact he.2.1
        · exact he.2.2.1
        · exact he.2.2.2
      rcases hne with ha | hb | hc | hd <;> positivity
    have hleft : -(a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤ 2 * (a * d - b * c) := by
      nlinarith only [sq_nonneg (a + d), sq_nonneg (b - c)]
    have hright : 2 * (a * d - b * c) ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
      nlinarith only [sq_nonneg (a - d), sq_nonneg (b + c)]
    have hbnd := mul_lt_mul_of_pos_right ht hs
    have hquad := abs_le.mpr ⟨hleft, hright⟩
    have hm := mul_le_mul_of_nonneg_left hquad (abs_nonneg t)
    rw [← abs_mul] at hm
    linarith only [neg_abs_le (t * (2 * (a * d - b * c))), hm, hbnd]

/-- Strictly positive real density matrices with equal readings for every local product. -/
theorem real_density_blind_spot :
    rhoPlus.PosDef ∧ rhoMinus.PosDef ∧ rhoPlus.trace = 1 ∧ rhoMinus.trace = 1 ∧
    rhoPlus ≠ rhoMinus ∧
    ∀ A B : Matrix (Fin 2) (Fin 2) ℝ, A.IsSymm → B.IsSymm →
      ((A ⊗ₖ B) * rhoPlus).trace = ((A ⊗ₖ B) * rhoMinus).trace := by
  refine ⟨quarterMix_posDef _ (by norm_num), quarterMix_posDef _ (by norm_num),
    quarterMix_trace _, quarterMix_trace _, ?_, ?_⟩
  · intro h
    have hentry := congrFun₂ h (0, 0) (1, 1)
    norm_num [rhoPlus, rhoMinus, quarterMix, W, Matrix.kronecker_apply, J₂,
      Matrix.one_apply] at hentry
  · intro A B hA hB
    simp [rhoPlus, rhoMinus, quarterMix, Matrix.mul_add,
      Matrix.trace_add, Matrix.trace_smul, blind_spot_trace A B hA hB]

end D5.S3.Quantum.Gauge.ComplexLocalTomography
