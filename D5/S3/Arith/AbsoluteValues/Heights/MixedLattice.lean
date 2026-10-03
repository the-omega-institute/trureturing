/- GID: D5/S3/Arith/AbsoluteValues/Heights/MixedLattice
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/MixedLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The mixed Gram determinant equals the archimedean Pluecker height factor. -/
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
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Complex

public section

noncomputable section

namespace NumberField.mixedEmbedding

open Module MeasureTheory Matrix NumberField.InfinitePlace
open scoped ComplexConjugate

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- The **real trace functional** on the mixed space: the sum of the real coordinates and of the
real parts of the complex ones. It is the functional for which the euclidean inner product of the
mixed space is `⟪a, b⟫ = mixedTrace (star a * b)`, so that multiplication by an element of the
mixed space has `star` for its adjoint. -/
@[expose] def mixedTrace : mixedSpace K →ₗ[ℝ] ℝ where
  toFun z := (∑ w, z.1 w) + ∑ w, (z.2 w).re
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.add_re, Finset.sum_add_distrib]
    ring
  map_smul' c a := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, RingHom.id_apply,
      mul_add, Finset.mul_sum]

variable {K}

variable (K)

open scoped Classical in
/-- The mixed space of `ι`-tuples, as a euclidean space: this is the ambient in which the lattice
of integral points of a subspace of `Kⁱ` lives. -/
abbrev mixedPi (ι : Type*) := PiLp 2 (fun _ : ι ↦ euclidean.mixedSpace K)

open scoped Classical in
/-- Reading a tuple of mixed-space points as a point of the euclidean tuple space. -/
@[expose] def toMixedPi (ι : Type*) : (ι → mixedSpace K) ≃ₗ[ℝ] mixedPi K ι :=
  (LinearEquiv.piCongrRight fun _ ↦ (euclidean.toMixed K).symm.toLinearEquiv).trans
    (WithLp.linearEquiv 2 ℝ (∀ _ : ι, euclidean.mixedSpace K)).symm

open scoped Classical in
/-- The Borel structure of the euclidean tuple space, declared once so that instance search does
not have to rediscover it through the nested `WithLp` structure at every use site. -/
instance instBorelSpaceMixedPi (ι : Type*) [Finite ι] : BorelSpace (mixedPi K ι) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  infer_instance

open scoped Classical in
/-- The euclidean tuple space is finite-dimensional, declared once for the same reason. -/
instance instFiniteDimensionalMixedPi (ι : Type*) [Finite ι] :
    FiniteDimensional ℝ (mixedPi K ι) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  infer_instance

variable {K}

section Matrices

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

open scoped Classical in
/-- The `ℝ`-linear map of euclidean tuple spaces attached to a matrix over the mixed space. -/
@[expose] def mixedPiMap (Y : Matrix κ ι (mixedSpace K)) : mixedPi K κ →ₗ[ℝ] mixedPi K ι :=
  (toMixedPi K ι).toLinearMap ∘ₗ (LinearMap.restrictScalars ℝ (Matrix.toLin' Yᵀ)) ∘ₗ
    (toMixedPi K κ).symm.toLinearMap

open scoped Classical in
/-- The self-adjoint endomorphism `Y Yᴴ` attached to a matrix over the mixed space. -/
@[expose] def mixedPiEnd (Y : Matrix κ ι (mixedSpace K)) : mixedPi K κ →ₗ[ℝ] mixedPi K κ :=
  (toMixedPi K κ).toLinearMap ∘ₗ (LinearMap.restrictScalars ℝ (Matrix.toLin' ((Y * Yᴴ)ᵀ))) ∘ₗ
    (toMixedPi K κ).symm.toLinearMap

end Matrices

section Archimedean

open exteriorPower

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

open scoped Classical in
set_option maxHeartbeats 1600000 in
/-- **Schmidt's Lemma 4, the local content.** The algebra norm of the Gram determinant of the
mixed embedding of a matrix over `K` is the archimedean local factor of the Arakelov height of its
Plücker point, with each infinite place weighted by its multiplicity. -/
theorem norm_det_gram (Y : Matrix (Fin m) ι K) :
    Algebra.norm ℝ ((Y.map (mixedEmbedding K)) * (Y.map (mixedEmbedding K))ᴴ).det
      = ∏ w : InfinitePlace K,
        (∑ s : Set.powersetCard ι m, w (plucker m Y.row s) ^ 2) ^ w.mult := by
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
  have hNormMixed (z : mixedSpace K) :
      Algebra.norm ℝ z = (∏ w, z.1 w) * ∏ w, Complex.normSq (z.2 w) := by
    have hNormProd (x : mixedSpace K) :
        Algebra.norm ℝ x = Algebra.norm ℝ x.1 * Algebra.norm ℝ x.2 := by
      have h : (LinearMap.mul ℝ (mixedSpace K)) x
          = LinearMap.prodMap (LinearMap.mul ℝ ({w : InfinitePlace K // IsReal w} → ℝ) x.1) (LinearMap.mul ℝ ({w : InfinitePlace K // IsComplex w} → ℂ) x.2) :=
        LinearMap.ext fun _ ↦ rfl
      rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, show
        (Algebra.lmul ℝ (mixedSpace K)) x = (LinearMap.mul ℝ (mixedSpace K)) x from rfl, h, LinearMap.det_prodMap]
      rfl

    have hNormPiReal (x : {w : InfinitePlace K // IsReal w} → ℝ) :
        Algebra.norm ℝ x = ∏ i, Algebra.norm ℝ (x i) := by
      classical
      set b := Module.Free.chooseBasis ℝ ℝ with hb
      set B := Pi.basis (fun _ : {w : InfinitePlace K // IsReal w} ↦ b) with hB
      set e : ((_ : {w : InfinitePlace K // IsReal w}) × Module.Free.ChooseBasisIndex ℝ ℝ) ≃
          (Module.Free.ChooseBasisIndex ℝ ℝ × {w : InfinitePlace K // IsReal w}) :=
        (Equiv.sigmaEquivProd {w : InfinitePlace K // IsReal w} _).trans (Equiv.prodComm {w : InfinitePlace K // IsReal w} _) with he
      have key : Algebra.leftMulMatrix B x
          = (Matrix.blockDiagonal (fun i ↦ Algebra.leftMulMatrix b (x i))).submatrix e e := by
        ext ⟨i, k⟩ ⟨j, l⟩
        rw [Algebra.leftMulMatrix_apply, Algebra.toMatrix_lmul' B x]
        simp only [Matrix.submatrix_apply, he, Equiv.trans_apply, Equiv.sigmaEquivProd_apply,
          Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.blockDiagonal_apply]
        rw [hB, Pi.basis_apply, Pi.basis_repr]
        by_cases h : i = j
        · subst h
          simp only [Pi.mul_apply, Pi.single_eq_same, Algebra.leftMulMatrix_apply,
            Algebra.toMatrix_lmul', ite_true]
        · simp [h]
      rw [Algebra.norm_eq_matrix_det B, key, Matrix.det_submatrix_equiv_self,
        Matrix.det_blockDiagonal]
      exact Finset.prod_congr rfl fun i _ ↦ (Algebra.norm_eq_matrix_det b (x i)).symm
    have hNormPiComplex (x : {w : InfinitePlace K // IsComplex w} → ℂ) :
        Algebra.norm ℝ x = ∏ i, Algebra.norm ℝ (x i) := by
      classical
      set b := Module.Free.chooseBasis ℝ ℂ with hb
      set B := Pi.basis (fun _ : {w : InfinitePlace K // IsComplex w} ↦ b) with hB
      set e : ((_ : {w : InfinitePlace K // IsComplex w}) × Module.Free.ChooseBasisIndex ℝ ℂ) ≃
          (Module.Free.ChooseBasisIndex ℝ ℂ × {w : InfinitePlace K // IsComplex w}) :=
        (Equiv.sigmaEquivProd {w : InfinitePlace K // IsComplex w} _).trans (Equiv.prodComm {w : InfinitePlace K // IsComplex w} _) with he
      have key : Algebra.leftMulMatrix B x
          = (Matrix.blockDiagonal (fun i ↦ Algebra.leftMulMatrix b (x i))).submatrix e e := by
        ext ⟨i, k⟩ ⟨j, l⟩
        rw [Algebra.leftMulMatrix_apply, Algebra.toMatrix_lmul' B x]
        simp only [Matrix.submatrix_apply, he, Equiv.trans_apply, Equiv.sigmaEquivProd_apply,
          Equiv.prodComm_apply, Prod.swap_prod_mk, Matrix.blockDiagonal_apply]
        rw [hB, Pi.basis_apply, Pi.basis_repr]
        by_cases h : i = j
        · subst h
          simp only [Pi.mul_apply, Pi.single_eq_same, Algebra.leftMulMatrix_apply,
            Algebra.toMatrix_lmul', ite_true]
        · simp [h]
      rw [Algebra.norm_eq_matrix_det B, key, Matrix.det_submatrix_equiv_self,
        Matrix.det_blockDiagonal]
      exact Finset.prod_congr rfl fun i _ ↦ (Algebra.norm_eq_matrix_det b (x i)).symm
    rw [hNormProd, hNormPiReal, hNormPiComplex]
    congr 1
    · refine Finset.prod_congr rfl fun w _ ↦ ?_
      have h := Algebra.norm_algebraMap (R := ℝ) (S := ℝ) (z.1 w)
      rwa [Module.finrank_self, pow_one, Algebra.algebraMap_self_apply] at h
    · exact Finset.prod_congr rfl fun w _ ↦ Algebra.norm_complex_apply _
  classical
  set p : Set.powersetCard ι m → K := plucker m Y.row with hp
  set z : mixedSpace K := ∑ s, (mixedEmbedding K (p s)) * star (mixedEmbedding K (p s)) with hz
  have hdet : ((Y.map (mixedEmbedding K)) * (Y.map (mixedEmbedding K))ᴴ).det = z := by
    rw [nativeSource39, hz]
    exact Finset.sum_congr rfl fun s _ ↦ by rw [nativeSource38]
  have h1 : ∀ w : {w : InfinitePlace K // IsReal w},
      z.1 w = ∑ s : Set.powersetCard ι m, w.1 (p s) ^ 2 := by
    intro w
    rw [hz]
    simp only [Prod.fst_sum, Finset.sum_apply, Prod.fst_mul, Pi.mul_apply, Prod.fst_star, Pi.star_apply, star_trivial]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have hw : w.1 (p s) = ‖(mixedEmbedding K (p s)).1 ⟨w.1, w.2⟩‖ := by
      rw [← normAtPlace_apply_of_isReal w.2, normAtPlace_apply]
    rw [hw, Real.norm_eq_abs, sq_abs, sq]
  have h2 : ∀ w : {w : InfinitePlace K // IsComplex w},
      Complex.normSq (z.2 w) = (∑ s : Set.powersetCard ι m, w.1 (p s) ^ 2) ^ 2 := by
    intro w
    have hzw : z.2 w = ((∑ s : Set.powersetCard ι m, w.1 (p s) ^ 2 : ℝ) : ℂ) := by
      rw [hz]
      simp only [Prod.snd_sum, Finset.sum_apply, Prod.snd_mul, Pi.mul_apply, Prod.snd_star, Pi.star_apply, Complex.star_def]
      push_cast
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      have hw : w.1 (p s) = ‖(mixedEmbedding K (p s)).2 ⟨w.1, w.2⟩‖ := by
        rw [← normAtPlace_apply_of_isComplex w.2, normAtPlace_apply]
      rw [hw, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hzw, Complex.normSq_ofReal, sq]
  rw [hdet, hNormMixed, InfinitePlace.prod_eq_prod_mul_prod]
  congr 1
  · exact Finset.prod_congr rfl fun w _ ↦ by rw [h1 w, InfinitePlace.mult_isReal, pow_one]
  · exact Finset.prod_congr rfl fun w _ ↦ by rw [h2 w, InfinitePlace.mult_isComplex]

end Archimedean

end NumberField.mixedEmbedding

end

end
