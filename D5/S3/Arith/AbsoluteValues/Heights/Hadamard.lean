/- GID: D5/S3/Arith/AbsoluteValues/Heights/Hadamard
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/Hadamard
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A complex Pluecker row norm is bounded by a product of row norms. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.Duality
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Sum.Order
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

-- Used only inside proofs: the lexicographic order on a sum type, the criterion for a vanishing
-- determinant, and the definiteness of the dot product over an ordered ring.

public section

namespace Matrix

open Module exteriorPower

section Submatrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {q : ℕ}

end Submatrix

section Monotone

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {q : ℕ}

set_option maxHeartbeats 1600000 in
/-- **Deleting columns does not increase the Gram determinant.** By Cauchy–Binet each side is a sum
of squares of maximal minors, and the minors on the left are some of the minors on the right. -/
theorem det_mul_transpose_self_submatrix_le {κ : Type*} [Fintype κ] [LinearOrder κ]
    (B : Matrix (Fin q) κ K) (f : ι ↪o κ) :
    ((B.submatrix id f) * (B.submatrix id f)ᵀ).det ≤ (B * Bᵀ).det := by
  classical
  have hFull : (B * Bᵀ).det =
      ∑ t : Set.powersetCard κ q, plucker q B.row t ^ 2 := by
    have nativeSource32 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : DecidableEq ι] (x y : ι → R) => (show (Pi.basisFun R ι).toDual x y = x ⬝ᵥ y from by
      classical
      conv_lhs => rw [← (Pi.basisFun R ι).sum_repr y]
      rw [map_sum]
      simp only [map_smul, Module.Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul, dotProduct]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _)))
    have nativeSource33 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Finite ι] [instSource4 : LinearOrder ι] (k : ℕ) (s : Set.powersetCard ι k)
        (y : ⋀[R]^k (ι → R)) => (show exteriorPower.pairingDual R (ι → R) k
            (exteriorPower.map k (Pi.basisFun R ι).toDual ((Pi.basisFun R ι).exteriorPower k s)) y
          = ((Pi.basisFun R ι).exteriorPower k).repr y s from by
      classical
      rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
        show (Pi.basisFun R ι).toDual ∘ (Pi.basisFun R ι) = (Pi.basisFun R ι).coord from
          _root_.funext fun i ↦ Module.Basis.coe_toDual_self _ i, basis_repr_apply]
      rfl)))
    have nativeSource34 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (x y : ⋀[R]^k (ι → R)) => (show exteriorPower.pairingDual R (ι → R) k (exteriorPower.map k (Pi.basisFun R ι).toDual x) y
          = ∑ s : Set.powersetCard ι k, ((Pi.basisFun R ι).exteriorPower k).repr x s *
              ((Pi.basisFun R ι).exteriorPower k).repr y s from by
      classical
      conv_lhs => rw [← ((Pi.basisFun R ι).exteriorPower k).sum_repr x]
      rw [map_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [map_smul, map_smul, LinearMap.smul_apply, nativeSource33, smul_eq_mul])))
    have nativeSource35 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (v w : Fin k → (ι → R)) => (show ∑ s : Set.powersetCard ι k, exteriorPower.plucker k v s * exteriorPower.plucker k w s
          = (Matrix.of fun i j ↦ v i ⬝ᵥ w j).det from by
      classical
      have h := nativeSource34 k (exteriorPower.ιMulti R k v) (exteriorPower.ιMulti R k w)
      rw [exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti] at h
      simp only [exteriorPower.plucker, Basis.equivFun_apply]
      rw [← h]
      simp only [Function.comp_apply, nativeSource32]
      rw [← Matrix.det_transpose (Matrix.of fun i j ↦ v i ⬝ᵥ w j)]
      apply congrArg Matrix.det
      ext i j
      exact nativeSource32 (v j) (w i))))
    have nativeSource36 := (open Module exteriorPower in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {m : ℕ} (A B : Matrix (Fin m) ι R) => (show (A * Bᵀ).det = ∑ s : Set.powersetCard ι m, exteriorPower.plucker m A.row s * exteriorPower.plucker m B.row s from by
      classical
      exact (
        (nativeSource35 m A.row B.row).symm
      ))))
    have nativeSource41 := (open Module exteriorPower in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {m : ℕ} (A : Matrix (Fin m) ι R) => (show (A * Aᵀ).det = ∑ s : Set.powersetCard ι m, exteriorPower.plucker m A.row s ^ 2 from by
      classical
      rw [nativeSource36]
      exact Finset.sum_congr rfl fun s _ ↦ (sq _).symm)))
    exact nativeSource41 B
  have hSub : ((B.submatrix id f) * (B.submatrix id f)ᵀ).det =
      ∑ t : Set.powersetCard ι q, plucker q (B.submatrix id f).row t ^ 2 := by
    have nativeSource32 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : DecidableEq ι] (x y : ι → R) => (show (Pi.basisFun R ι).toDual x y = x ⬝ᵥ y from by
      classical
      conv_lhs => rw [← (Pi.basisFun R ι).sum_repr y]
      rw [map_sum]
      simp only [map_smul, Module.Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul, dotProduct]
      exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _)))
    have nativeSource33 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Finite ι] [instSource4 : LinearOrder ι] (k : ℕ) (s : Set.powersetCard ι k)
        (y : ⋀[R]^k (ι → R)) => (show exteriorPower.pairingDual R (ι → R) k
            (exteriorPower.map k (Pi.basisFun R ι).toDual ((Pi.basisFun R ι).exteriorPower k s)) y
          = ((Pi.basisFun R ι).exteriorPower k).repr y s from by
      classical
      rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
        show (Pi.basisFun R ι).toDual ∘ (Pi.basisFun R ι) = (Pi.basisFun R ι).coord from
          _root_.funext fun i ↦ Module.Basis.coe_toDual_self _ i, basis_repr_apply]
      rfl)))
    have nativeSource34 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (x y : ⋀[R]^k (ι → R)) => (show exteriorPower.pairingDual R (ι → R) k (exteriorPower.map k (Pi.basisFun R ι).toDual x) y
          = ∑ s : Set.powersetCard ι k, ((Pi.basisFun R ι).exteriorPower k).repr x s *
              ((Pi.basisFun R ι).exteriorPower k).repr y s from by
      classical
      conv_lhs => rw [← ((Pi.basisFun R ι).exteriorPower k).sum_repr x]
      rw [map_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [map_smul, map_smul, LinearMap.smul_apply, nativeSource33, smul_eq_mul])))
    have nativeSource35 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (v w : Fin k → (ι → R)) => (show ∑ s : Set.powersetCard ι k, exteriorPower.plucker k v s * exteriorPower.plucker k w s
          = (Matrix.of fun i j ↦ v i ⬝ᵥ w j).det from by
      classical
      have h := nativeSource34 k (exteriorPower.ιMulti R k v) (exteriorPower.ιMulti R k w)
      rw [exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti] at h
      simp only [exteriorPower.plucker, Basis.equivFun_apply]
      rw [← h]
      simp only [Function.comp_apply, nativeSource32]
      rw [← Matrix.det_transpose (Matrix.of fun i j ↦ v i ⬝ᵥ w j)]
      apply congrArg Matrix.det
      ext i j
      exact nativeSource32 (v j) (w i))))
    have nativeSource36 := (open Module exteriorPower in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {m : ℕ} (A B : Matrix (Fin m) ι R) => (show (A * Bᵀ).det = ∑ s : Set.powersetCard ι m, exteriorPower.plucker m A.row s * exteriorPower.plucker m B.row s from by
      classical
      exact (
        (nativeSource35 m A.row B.row).symm
      ))))
    have nativeSource41 := (open Module exteriorPower in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {m : ℕ} (A : Matrix (Fin m) ι R) => (show (A * Aᵀ).det = ∑ s : Set.powersetCard ι m, exteriorPower.plucker m A.row s ^ 2 from by
      classical
      rw [nativeSource36]
      exact Finset.sum_congr rfl fun s _ ↦ (sq _).symm)))
    exact nativeSource41 (B.submatrix id f)
  rw [hSub, hFull]
  set F : Set.powersetCard ι q → Set.powersetCard κ q := fun s ↦
    ⟨(s : Finset ι).map f.toEmbedding, Set.powersetCard.mem_iff.2 (by
      simp [Set.powersetCard.card_eq s])⟩ with hFdef
  have hF : Function.Injective F := fun s t h ↦
    Subtype.ext (Finset.map_injective _ (congrArg Subtype.val h))
  have hplucker (s : Set.powersetCard ι q) :
      plucker q (B.submatrix id f).row s = plucker q B.row (F s) := by
    have hLeft : plucker q (B.submatrix id f).row s =
        (Matrix.of fun i j ↦ (B.submatrix id f).row i
          (Set.powersetCard.ofFinEmbEquiv.symm s j)).det := by
      classical
      rw [exteriorPower.plucker, Module.Basis.equivFun_apply,
        exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
      simp
    have hRight : plucker q B.row (F s) =
        (Matrix.of fun i j ↦ B.row i
          (Set.powersetCard.ofFinEmbEquiv.symm (F s) j)).det := by
      classical
      rw [exteriorPower.plucker, Module.Basis.equivFun_apply,
        exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
      simp
    rw [hLeft, hRight, Set.powersetCard.ofFinEmbEquiv_symm_apply,
      Set.powersetCard.ofFinEmbEquiv_symm_apply]
    congr 1
    funext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.row]
    congr 1
    exact congrFun (Finset.orderEmbOfFin_unique _
      (fun x ↦ Finset.mem_map_of_mem _ (Finset.orderEmbOfFin_mem _ _ x))
      (f.strictMono.comp (Finset.orderEmbOfFin _ _).strictMono)) j
  calc ∑ s : Set.powersetCard ι q, plucker q (B.submatrix id f).row s ^ 2
      = ∑ s : Set.powersetCard ι q, plucker q B.row (F s) ^ 2 :=
        Finset.sum_congr rfl fun s _ ↦ by rw [hplucker]
    _ = ∑ t ∈ Finset.image F Finset.univ, plucker q B.row t ^ 2 :=
        (Finset.sum_image (f := fun t ↦ plucker q B.row t ^ 2) fun x _ y _ h ↦ hF h).symm
    _ ≤ ∑ t : Set.powersetCard κ q, plucker q B.row t ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ ↦ sq_nonneg _

/-- **Minkowski's monotonicity, in the case needed.** Adding a Gram matrix to a Gram matrix does not
decrease the determinant: the sum is the Gram matrix of the two matrices side by side, and deleting
the second block of columns is the previous lemma. -/
theorem det_mul_transpose_self_le_det_add (V W : Matrix (Fin q) ι K) :
    (V * Vᵀ).det ≤ (V * Vᵀ + W * Wᵀ).det := by
  set B : Matrix (Fin q) (ι ⊕ₗ ι) K := Matrix.of fun i j ↦ Sum.elim (V i) (W i) (ofLex j) with hB
  have h1 : B.submatrix id (OrderEmbedding.ofStrictMono (⇑toLex ∘ Sum.inl)
      Sum.Lex.inl_strictMono) = V := rfl
  have h2 : B * Bᵀ = V * Vᵀ + W * Wᵀ := by
    ext i j
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
      show (∑ c : ι ⊕ₗ ι, B i c * Bᵀ c j) = ∑ c : ι ⊕ ι, B i (toLex c) * Bᵀ (toLex c) j from
        Fintype.sum_equiv (toLex (α := ι ⊕ ι)) _ _ fun c ↦ rfl, Fintype.sum_sum_type]
    rfl
  have h := det_mul_transpose_self_submatrix_le B
    (OrderEmbedding.ofStrictMono (⇑toLex ∘ Sum.inl) Sum.Lex.inl_strictMono)
  rwa [h1, h2] at h

end Monotone

section Hadamard

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {p q : ℕ}

set_option maxHeartbeats 1600000 in
/-- **The generalized Hadamard inequality**, also called the Fischer inequality: cutting the rows of
a matrix into two blocks can only increase the product of the Gram determinants. Equivalently, by
Cauchy–Binet, the ℓ² norm of the tuple of maximal minors is submultiplicative under cutting the
rows. -/
theorem det_mul_transpose_self_fromRows_le (A : Matrix (Fin p) ι K) (B : Matrix (Fin q) ι K) :
    ((fromRows A B) * (fromRows A B)ᵀ).det ≤ (A * Aᵀ).det * (B * Bᵀ).det := by
  have nativeSource32 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : DecidableEq ι] (x y : ι → R) => (show (Pi.basisFun R ι).toDual x y = x ⬝ᵥ y from by
    classical
    conv_lhs => rw [← (Pi.basisFun R ι).sum_repr y]
    rw [map_sum]
    simp only [map_smul, Module.Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul, dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _)))
  have nativeSource33 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Finite ι] [instSource4 : LinearOrder ι] (k : ℕ) (s : Set.powersetCard ι k)
      (y : ⋀[R]^k (ι → R)) => (show exteriorPower.pairingDual R (ι → R) k
          (exteriorPower.map k (Pi.basisFun R ι).toDual ((Pi.basisFun R ι).exteriorPower k s)) y
        = ((Pi.basisFun R ι).exteriorPower k).repr y s from by
    classical
    rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
      show (Pi.basisFun R ι).toDual ∘ (Pi.basisFun R ι) = (Pi.basisFun R ι).coord from
        _root_.funext fun i ↦ Module.Basis.coe_toDual_self _ i, basis_repr_apply]
    rfl)))
  have nativeSource34 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (x y : ⋀[R]^k (ι → R)) => (show exteriorPower.pairingDual R (ι → R) k (exteriorPower.map k (Pi.basisFun R ι).toDual x) y
        = ∑ s : Set.powersetCard ι k, ((Pi.basisFun R ι).exteriorPower k).repr x s *
            ((Pi.basisFun R ι).exteriorPower k).repr y s from by
    classical
    conv_lhs => rw [← ((Pi.basisFun R ι).exteriorPower k).sum_repr x]
    rw [map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, nativeSource33, smul_eq_mul])))
  have nativeSource35 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (v w : Fin k → (ι → R)) => (show ∑ s : Set.powersetCard ι k, exteriorPower.plucker k v s * exteriorPower.plucker k w s
        = (Matrix.of fun i j ↦ v i ⬝ᵥ w j).det from by
    classical
    have h := nativeSource34 k (exteriorPower.ιMulti R k v) (exteriorPower.ιMulti R k w)
    rw [exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti] at h
    simp only [exteriorPower.plucker, Basis.equivFun_apply]
    rw [← h]
    simp only [Function.comp_apply, nativeSource32]
    rw [← Matrix.det_transpose (Matrix.of fun i j ↦ v i ⬝ᵥ w j)]
    apply congrArg Matrix.det
    ext i j
    exact nativeSource32 (v j) (w i))))
  have nativeSource36 := (open Module exteriorPower in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {m : ℕ} (A B : Matrix (Fin m) ι R) => (show (A * Bᵀ).det = ∑ s : Set.powersetCard ι m, exteriorPower.plucker m A.row s * exteriorPower.plucker m B.row s from by
    classical
    exact (
      (nativeSource35 m A.row B.row).symm
    ))))
  have nativeSource41 := (open Module exteriorPower in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {m : ℕ} (A : Matrix (Fin m) ι R) => (show (A * Aᵀ).det = ∑ s : Set.powersetCard ι m, exteriorPower.plucker m A.row s ^ 2 from by
    classical
    rw [nativeSource36]
    exact Finset.sum_congr rfl fun s _ ↦ (sq _).symm)))
  have nativeSource42 := (open Module exteriorPower in (fun {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {m : ℕ} {S : Type _} [instSource7 : CommRing S] [instSource8 : LinearOrder S] [instSource9 : IsStrictOrderedRing S] (A : Matrix (Fin m) ι S) => (show 0 ≤ (A * Aᵀ).det from by
    classical
    rw [nativeSource41]
    exact Finset.sum_nonneg fun s _ ↦ sq_nonneg _)))
  rcases eq_or_ne (A * Aᵀ).det 0 with hA | hA
  · -- The first block is degenerate: both sides vanish.
    rw [hA, zero_mul]
    refine le_of_eq ?_
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hA
    have hx : (c ᵥ* A) ᵥ* Aᵀ = 0 := by rw [Matrix.vecMul_vecMul]; exact hc
    have h2 : (c ᵥ* A) ⬝ᵥ (c ᵥ* A) = 0 := by
      nth_rewrite 2 [← Matrix.mulVec_transpose]
      rw [Matrix.dotProduct_mulVec, hx, zero_dotProduct]
    have hcA : c ᵥ* A = 0 := dotProduct_self_eq_zero.1 h2
    refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨Sum.elim c 0, ?_, ?_⟩
    · exact fun h ↦ hc0 (_root_.funext fun i ↦ congrFun h (Sum.inl i))
    · rw [← Matrix.vecMul_vecMul, Matrix.vecMul_fromRows]
      simp [hcA]
  · -- Project the second block orthogonally to the first.
    have hAu : IsUnit (A * Aᵀ).det := isUnit_iff_ne_zero.2 hA
    set X : Matrix (Fin q) (Fin p) K := B * Aᵀ * (A * Aᵀ)⁻¹ with hX
    set B' : Matrix (Fin q) ι K := B - X * A with hB'
    have hXA : X * (A * Aᵀ) = B * Aᵀ := by
      rw [hX, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]
    have hB'A : B' * Aᵀ = 0 := by
      rw [hB', Matrix.sub_mul, Matrix.mul_assoc, hXA, sub_self]
    have hAB' : A * B'ᵀ = 0 := by
      have h := congrArg Matrix.transpose hB'A
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h
    -- The projection is a row operation of determinant `1`.
    have hUdet : (fromBlocks (1 : Matrix (Fin p) (Fin p) K) 0 (-X) 1).det = 1 := by
      rw [Matrix.det_fromBlocks_zero₁₂]
      simp
    have hUM : (fromBlocks (1 : Matrix (Fin p) (Fin p) K) 0 (-X) 1) * fromRows A B
        = fromRows A B' := by
      rw [Matrix.fromBlocks_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero,
        Matrix.one_mul, Matrix.neg_mul, hB']
      congr 1
      abel
    have key : ((fromRows A B') * (fromRows A B')ᵀ).det = (A * Aᵀ).det * (B' * B'ᵀ).det := by
      rw [Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols, hAB',
        Matrix.det_fromBlocks_zero₁₂]
    have hdetM : ((fromRows A B) * (fromRows A B)ᵀ).det
        = ((fromRows A B') * (fromRows A B')ᵀ).det := by
      rw [← hUM, Matrix.transpose_mul, ← Matrix.mul_assoc,
        Matrix.mul_assoc _ (fromRows A B) _, Matrix.det_mul, Matrix.det_mul,
        Matrix.det_transpose, hUdet, one_mul, mul_one]
    -- The projected block has the smaller Gram determinant.
    have hBeq : B = B' + X * A := by rw [hB']; abel
    have hY1 : B' * (X * A)ᵀ = 0 := by
      rw [Matrix.transpose_mul, ← Matrix.mul_assoc, hB'A, Matrix.zero_mul]
    have hY2 : (X * A) * B'ᵀ = 0 := by rw [Matrix.mul_assoc, hAB', Matrix.mul_zero]
    have hsplit : B * Bᵀ = B' * B'ᵀ + (X * A) * (X * A)ᵀ := by
      conv_lhs => rw [hBeq]
      rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hY1, hY2]
      abel
    calc ((fromRows A B) * (fromRows A B)ᵀ).det = (A * Aᵀ).det * (B' * B'ᵀ).det := by
          rw [hdetM, key]
      _ ≤ (A * Aᵀ).det * (B * Bᵀ).det := by
          refine mul_le_mul_of_nonneg_left ?_ (nativeSource42 A)
          rw [hsplit]
          exact det_mul_transpose_self_le_det_add B' (X * A)

/-- **Hadamard's inequality.** The Gram determinant of the rows is at most the product of their
squared lengths: the fully split case of the generalized inequality, by induction on the number of
rows. This is the form Layer 5.5 uses to trade the height of the row space for the heights of the
individual rows. -/
theorem det_mul_transpose_self_le_prod {m : ℕ} (A : Matrix (Fin m) ι K) :
    (A * Aᵀ).det ≤ ∏ i, A.row i ⬝ᵥ A.row i := by
  induction m with
  | zero => simp
  | succ m ih =>
      set A' : Matrix (Fin m) ι K := A.submatrix Fin.castSucc id with hA'
      set a : Matrix (Fin 1) ι K := A.submatrix (fun _ ↦ Fin.last m) id with ha
      have hfr : fromRows A' a = A.submatrix finSumFinEquiv id := by
        ext (i | i) j
        · rfl
        · have hi : i = 0 := Subsingleton.elim _ _
          subst hi
          rfl
      have hre : (A.submatrix finSumFinEquiv id) * (A.submatrix finSumFinEquiv id)ᵀ
          = (A * Aᵀ).submatrix finSumFinEquiv finSumFinEquiv := by
        ext i j
        simp [Matrix.mul_apply]
      have h1 : (a * aᵀ).det = A.row (Fin.last m) ⬝ᵥ A.row (Fin.last m) := by
        rw [Matrix.det_fin_one]
        rfl
      calc (A * Aᵀ).det = ((fromRows A' a) * (fromRows A' a)ᵀ).det := by
            rw [hfr, hre, Matrix.det_submatrix_equiv_self]
        _ ≤ (A' * A'ᵀ).det * (a * aᵀ).det := det_mul_transpose_self_fromRows_le A' a
        _ ≤ (∏ i : Fin m, A'.row i ⬝ᵥ A'.row i) * (a * aᵀ).det := by
            refine mul_le_mul_of_nonneg_right (ih A') ?_
            rw [h1]
            exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
        _ = ∏ i : Fin (m + 1), A.row i ⬝ᵥ A.row i := by
            rw [Fin.prod_univ_castSucc, h1]
            rfl

end Hadamard

section Square

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

end Square

section Complex

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m n : ℕ}

/-- The real part of the Hermitian Gram matrix `B Bᴴ`, written out as a sum so that no
`Complex.re` has to be pushed through one. -/
def reGram (B : Matrix (Fin m) ι ℂ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a a' ↦ ∑ j, ((B a j).re * (B a' j).re + (B a j).im * (B a' j).im)

/-- The imaginary part of the Hermitian Gram matrix `B Bᴴ`. -/
def imGram (B : Matrix (Fin m) ι ℂ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a a' ↦ ∑ j, ((B a j).im * (B a' j).re - (B a j).re * (B a' j).im)

/-- **The realification of a complex matrix**: the real `2m × 2n` matrix of the same linear map,
read on `ℂ ≅ ℝ²`. Its rows come in pairs `(X ᵢ, Y ᵢ)` and `(−Y ᵢ, X ᵢ)` of equal length, and its
Gram matrix is the realification of `B Bᴴ`, so the real Hadamard inequality applied to it is the
complex one squared. -/
def realify (B : Matrix (Fin m) ι ℂ) : Matrix (Fin m ⊕ Fin m) (ι ⊕ₗ ι) ℝ :=
  Matrix.of fun i j ↦
    Sum.elim (fun a ↦ Sum.elim (fun b ↦ (B a b).re) (fun b ↦ (B a b).im) (ofLex j))
      (fun a ↦ Sum.elim (fun b ↦ -(B a b).im) (fun b ↦ (B a b).re) (ofLex j)) i

omit [LinearOrder ι] in
/-- The Gram matrix of the realification is the realification of the Hermitian Gram matrix. -/
theorem realify_mul_transpose (B : Matrix (Fin m) ι ℂ) :
    realify B * (realify B)ᵀ =
      Matrix.fromBlocks (reGram B) (imGram B) (-(imGram B)) (reGram B) := by
  have hSumLex (f g f' g' : ι → ℝ) :
      (∑ j : ι ⊕ₗ ι, Sum.elim f g (ofLex j) * Sum.elim f' g' (ofLex j))
        = (∑ b, f b * f' b) + ∑ b, g b * g' b := by
    rw [show (∑ j : ι ⊕ₗ ι, Sum.elim f g (ofLex j) * Sum.elim f' g' (ofLex j))
        = ∑ c : ι ⊕ ι, Sum.elim f g c * Sum.elim f' g' c from
      Fintype.sum_equiv (toLex (α := ι ⊕ ι)) _ _ fun c ↦ rfl, Fintype.sum_sum_type]
    simp
  ext i k
  rw [Matrix.mul_apply]
  simp only [realify, Matrix.of_apply, Matrix.transpose_apply]
  cases i with
  | inl a => cases k with
    | inl a' =>
        simp only [Sum.elim_inl]
        rw [hSumLex, Matrix.fromBlocks_apply₁₁]
        simp only [reGram, Matrix.of_apply]
        rw [← Finset.sum_add_distrib]
    | inr a' =>
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [hSumLex, Matrix.fromBlocks_apply₁₂]
        simp only [imGram, Matrix.of_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
  | inr a => cases k with
    | inl a' =>
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [hSumLex, Matrix.fromBlocks_apply₂₁]
        simp only [imGram, Matrix.neg_apply, Matrix.of_apply]
        rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
    | inr a' =>
        simp only [Sum.elim_inr]
        rw [hSumLex, Matrix.fromBlocks_apply₂₂]
        simp only [reGram, Matrix.of_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by ring

omit [LinearOrder ι] in
/-- The Hermitian Gram matrix in terms of its real and imaginary parts. -/
theorem gram_eq_reGram_add (B : Matrix (Fin m) ι ℂ) :
    B * Bᴴ = (reGram B).map (↑) + Complex.I • (imGram B).map (↑) := by
  ext a a'
  rw [Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul]
  simp only [reGram, imGram, Matrix.of_apply, Complex.ofReal_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ (fun (z w : ℂ) ↦ (show z * (starRingEnd ℂ) w =
      ((z.re * w.re + z.im * w.im : ℝ) : ℂ) +
        Complex.I * ((z.im * w.re - z.re * w.im : ℝ) : ℂ) from by
        apply Complex.ext
        · simp [Complex.mul_re]
        · simp [Complex.mul_im]; ring)) _ _

omit [LinearOrder ι] in
/-- The transpose of the Hermitian Gram matrix is its entrywise conjugate, so the sign of the
imaginary part flips. -/
theorem gram_transpose_eq_reGram_sub (B : Matrix (Fin m) ι ℂ) :
    (B * Bᴴ)ᵀ = (reGram B).map (↑) - Complex.I • (imGram B).map (↑) := by
  ext a a'
  rw [Matrix.transpose_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.map_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  simp only [reGram, imGram, Matrix.of_apply, Complex.ofReal_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show Bᴴ j a = (starRingEnd ℂ) (B a j) from rfl, (fun (z w : ℂ) ↦ (show z * (starRingEnd ℂ) w =
      ((z.re * w.re + z.im * w.im : ℝ) : ℂ) +
        Complex.I * ((z.im * w.re - z.re * w.im : ℝ) : ℂ) from by
        apply Complex.ext
        · simp [Complex.mul_re]
        · simp [Complex.mul_im]; ring))]
  push_cast
  ring

/-- **The determinant of a realified matrix factors.** Two unipotent block row and column
operations bring `fromBlocks X Y (-Y) X` to block triangular form with diagonal blocks
`X − i Y` and `X + i Y`. -/
theorem det_fromBlocks_neg_comm (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.fromBlocks X Y (-Y) X).det
      = (X - Complex.I • Y).det * (X + Complex.I • Y).det := by
  set L : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    Matrix.fromBlocks 1 (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) 0 1 with hLdef
  set R : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    Matrix.fromBlocks 1 (-(Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))) 0 1 with hRdef
  have hL : L.det = 1 := by rw [hLdef, Matrix.det_fromBlocks_zero₂₁]; simp
  have hR : R.det = 1 := by rw [hRdef, Matrix.det_fromBlocks_zero₂₁]; simp
  have hmul : L * Matrix.fromBlocks X Y (-Y) X * R
      = Matrix.fromBlocks (X - Complex.I • Y) 0 (-Y) (X + Complex.I • Y) := by
    rw [hLdef, hRdef, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    congr 1 <;> simp [smul_smul, Complex.I_mul_I] <;> module
  have h := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, hL, hR, one_mul, mul_one,
    Matrix.det_fromBlocks_zero₁₂] at h
  exact h

omit [LinearOrder ι] in
/-- **The Gram determinant of the realification is the square of the Hermitian one.** The two
diagonal blocks of the factorization are `B Bᴴ` and its transpose, which have equal
determinants. -/
theorem det_realify_mul_transpose (B : Matrix (Fin m) ι ℂ) :
    (((realify B * (realify B)ᵀ).det : ℝ) : ℂ) = (B * Bᴴ).det ^ 2 := by
  rw [show (((realify B * (realify B)ᵀ).det : ℝ) : ℂ)
      = ((realify B * (realify B)ᵀ).map ((↑) : ℝ → ℂ)).det from
    Complex.ofRealHom.map_det _, realify_mul_transpose, Matrix.fromBlocks_map,
    show ((-(imGram B)).map ((↑) : ℝ → ℂ)) = -(imGram B).map (↑) by
      ext i j
      simp,
    det_fromBlocks_neg_comm, ← gram_transpose_eq_reGram_sub, ← gram_eq_reGram_add,
    Matrix.det_transpose, sq]

omit [LinearOrder ι] in
/-- Both rows of the realification attached to a row of `B` have that row's length. -/
theorem row_dotProduct_realify (B : Matrix (Fin m) ι ℂ) (i : Fin m ⊕ Fin m) :
    (realify B).row i ⬝ᵥ (realify B).row i = ∑ j, ‖B (Sum.elim id id i) j‖ ^ 2 := by
  have hSumLex (f g f' g' : ι → ℝ) :
      (∑ j : ι ⊕ₗ ι, Sum.elim f g (ofLex j) * Sum.elim f' g' (ofLex j))
        = (∑ b, f b * f' b) + ∑ b, g b * g' b := by
    rw [show (∑ j : ι ⊕ₗ ι, Sum.elim f g (ofLex j) * Sum.elim f' g' (ofLex j))
        = ∑ c : ι ⊕ ι, Sum.elim f g c * Sum.elim f' g' c from
      Fintype.sum_equiv (toLex (α := ι ⊕ ι)) _ _ fun c ↦ rfl, Fintype.sum_sum_type]
    simp
  cases i with
  | inl a =>
      change (∑ j : ι ⊕ₗ ι, _) = _
      simp only [realify, Matrix.row, Matrix.of_apply, Sum.elim_inl, id_eq]
      rw [hSumLex, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by
        rw [Complex.sq_norm, Complex.normSq_apply]
  | inr a =>
      change (∑ j : ι ⊕ₗ ι, _) = _
      simp only [realify, Matrix.row, Matrix.of_apply, Sum.elim_inr, id_eq]
      rw [hSumLex, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring

set_option maxHeartbeats 1600000 in
/-- **Hadamard's inequality at a complex place.** The ℓ² norm of the tuple of maximal minors of a
complex matrix is at most the product of the ℓ² norms of its rows — the statement Layer 5.5 needs
at a complex place, where the Gram matrix is `B Bᴴ` and not `B Bᵀ`.

It is deduced from the real inequality, not proved again: the realification has twice the rows,
each of the same length as the row of `B` it comes from, and its Gram determinant is the square of
the Hermitian one. Applied to the image of a matrix over a number field under the embedding of an
infinite place, this covers the real places too, since there the embedding is real and the
conjugate transpose is the transpose. -/
theorem sum_sq_norm_plucker_row_le_prod (B : Matrix (Fin m) ι ℂ) :
    ∑ s : Set.powersetCard ι m, ‖plucker m B.row s‖ ^ 2 ≤ ∏ i, ∑ j, ‖B i j‖ ^ 2 := by
  have nativeSource18 := (open Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (v : Fin k → (ι → R)) (s : Set.powersetCard ι k) => (show exteriorPower.plucker k v s = (Matrix.of fun i j ↦ v i (Set.powersetCard.ofFinEmbEquiv.symm s j)).det from by
    classical
    rw [exteriorPower.plucker, Module.Basis.equivFun_apply, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    simp)))
  have nativeSource32 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : DecidableEq ι] (x y : ι → R) => (show (Pi.basisFun R ι).toDual x y = x ⬝ᵥ y from by
    classical
    conv_lhs => rw [← (Pi.basisFun R ι).sum_repr y]
    rw [map_sum]
    simp only [map_smul, Module.Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul, dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _)))
  have nativeSource33 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Finite ι] [instSource4 : LinearOrder ι] (k : ℕ) (s : Set.powersetCard ι k)
      (y : ⋀[R]^k (ι → R)) => (show exteriorPower.pairingDual R (ι → R) k
          (exteriorPower.map k (Pi.basisFun R ι).toDual ((Pi.basisFun R ι).exteriorPower k s)) y
        = ((Pi.basisFun R ι).exteriorPower k).repr y s from by
    classical
    rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
      show (Pi.basisFun R ι).toDual ∘ (Pi.basisFun R ι) = (Pi.basisFun R ι).coord from
        _root_.funext fun i ↦ Module.Basis.coe_toDual_self _ i, basis_repr_apply]
    rfl)))
  have nativeSource34 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (x y : ⋀[R]^k (ι → R)) => (show exteriorPower.pairingDual R (ι → R) k (exteriorPower.map k (Pi.basisFun R ι).toDual x) y
        = ∑ s : Set.powersetCard ι k, ((Pi.basisFun R ι).exteriorPower k).repr x s *
            ((Pi.basisFun R ι).exteriorPower k).repr y s from by
    classical
    conv_lhs => rw [← ((Pi.basisFun R ι).exteriorPower k).sum_repr x]
    rw [map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, nativeSource33, smul_eq_mul])))
  have nativeSource35 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] (k : ℕ) (v w : Fin k → (ι → R)) => (show ∑ s : Set.powersetCard ι k, exteriorPower.plucker k v s * exteriorPower.plucker k w s
        = (Matrix.of fun i j ↦ v i ⬝ᵥ w j).det from by
    classical
    have h := nativeSource34 k (exteriorPower.ιMulti R k v) (exteriorPower.ιMulti R k w)
    rw [exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti] at h
    simp only [exteriorPower.plucker, Basis.equivFun_apply]
    rw [← h]
    simp only [Function.comp_apply, nativeSource32]
    rw [← Matrix.det_transpose (Matrix.of fun i j ↦ v i ⬝ᵥ w j)]
    apply congrArg Matrix.det
    ext i j
    exact nativeSource32 (v j) (w i))))
  have nativeSource36 := (open Module exteriorPower in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {m : ℕ} (A B : Matrix (Fin m) ι R) => (show (A * Bᵀ).det = ∑ s : Set.powersetCard ι m, exteriorPower.plucker m A.row s * exteriorPower.plucker m B.row s from by
    classical
    exact (
      (nativeSource35 m A.row B.row).symm
    ))))
  have nativeSource37 := (open Matrix Module in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {S : Type _} [CommRing S] (f : R →+* S) (k : ℕ) (v : Fin k → (ι → R))
      (s : Set.powersetCard ι k) => (show exteriorPower.plucker k (fun i ↦ f ∘ v i) s = f (exteriorPower.plucker k v s) from by
    classical
    rw [nativeSource18, nativeSource18, RingHom.map_det]
    rfl)))
  have nativeSource38 := (open Module exteriorPower in (fun {R : Type _} [instSource1 : CommRing R] {ι : Type _} [instSource3 : Fintype ι] [instSource4 : LinearOrder ι] {m : ℕ} {S : Type _} [CommRing S] (f : R →+* S) (A : Matrix (Fin m) ι R)
      (s : Set.powersetCard ι m) => (show exteriorPower.plucker m (A.map f).row s = f (exteriorPower.plucker m A.row s) from by
    classical
    exact (
      nativeSource37 f m A.row s
    ))))
  have nativeSource39 := (open Module exteriorPower in (fun {R : Type _} [instSource1 : CommRing R] [instSource2 : StarRing R] {ι : Type _} [instSource4 : Fintype ι] [instSource5 : LinearOrder ι] {m : ℕ} (A : Matrix (Fin m) ι R) => (show (A * Aᴴ).det =
        ∑ s : Set.powersetCard ι m, exteriorPower.plucker m A.row s * Star.star (exteriorPower.plucker m A.row s) from by
    classical
    rw [show Aᴴ = (A.map (starRingEnd R))ᵀ from rfl, nativeSource36]
    exact Finset.sum_congr rfl fun s _ ↦ by rw [nativeSource38]; rfl)))
  have nativeSource40 := (open Module exteriorPower in (fun {ι : Type _} [instSource4 : Fintype ι] [instSource5 : LinearOrder ι] {m : ℕ} {K : Type _} [instSource8 : RCLike K] (A : Matrix (Fin m) ι K) => (show (A * Aᴴ).det = ((∑ s : Set.powersetCard ι m, ‖exteriorPower.plucker m A.row s‖ ^ 2 : ℝ) : K) from by
    classical
    rw [nativeSource39]
    push_cast
    exact Finset.sum_congr rfl fun s _ ↦ RCLike.mul_conj _)))
  set S : ℝ := ∑ s : Set.powersetCard ι m, ‖plucker m B.row s‖ ^ 2 with hS
  set T : ℝ := ∏ i, ∑ j, ‖B i j‖ ^ 2 with hT
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun s _ ↦ by positivity
  have hT0 : 0 ≤ T := Finset.prod_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by positivity
  set D : Matrix (Fin (m + m)) (ι ⊕ₗ ι) ℝ :=
    (realify B).submatrix ⇑finSumFinEquiv.symm id with hD
  have hDD : D * Dᵀ = (realify B * (realify B)ᵀ).submatrix
      ⇑finSumFinEquiv.symm ⇑finSumFinEquiv.symm := by
    ext i k
    simp [hD, Matrix.mul_apply]
  have hdet : (D * Dᵀ).det = S ^ 2 := by
    have h := det_realify_mul_transpose B
    rw [nativeSource40] at h
    rw [hDD, Matrix.det_submatrix_equiv_self, hS]
    exact Complex.ofReal_inj.mp (by push_cast at h ⊢; exact h)
  have hprod : ∏ i, D.row i ⬝ᵥ D.row i = T ^ 2 := by
    rw [show (∏ i, D.row i ⬝ᵥ D.row i)
        = ∏ i : Fin m ⊕ Fin m, (realify B).row i ⬝ᵥ (realify B).row i from
      Fintype.prod_equiv finSumFinEquiv.symm _ _ fun i ↦ rfl, Fintype.prod_sum_type]
    simp only [row_dotProduct_realify, Sum.elim_inl, Sum.elim_inr, id_eq]
    rw [hT, sq]
  have hle : S ^ 2 ≤ T ^ 2 := by
    rw [← hdet, ← hprod]
    exact Matrix.det_mul_transpose_self_le_prod D
  nlinarith [hle, hS0, hT0]

end Complex

end Matrix

section Examples

open Matrix exteriorPower

end Examples

end
