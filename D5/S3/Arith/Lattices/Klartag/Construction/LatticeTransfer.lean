/- GID: D5/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Construction/LatticeTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construction A lattices, covolumes and ellipsoid transfer. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib
import D5.S3.Arith.Lattices.Klartag.Walk.ChainEllipsoid

open Matrix
open MeasureTheory
open Metric
open Set

open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag.Construction.LatticeTransfer

open D5.S3.Arith.Lattices.Klartag.Walk.ChainEllipsoid

variable {n : ℕ}

/-- The origin is in every ellipsoid. -/
theorem zero_mem_ellipsoid (A : Matrix (Fin n) (Fin n) ℝ) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ ellipsoid A := by
  show _ < (1 : ℝ)
  simp

/-- **The congruence `A ↦ Bᵀ A B` pulls the ellipsoid back along `B`.** -/
theorem mem_ellipsoid_congr (A B : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    v ∈ ellipsoid (Bᵀ * A * B)
      ↔ (WithLp.toLp 2 (B *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin n)) ∈ ellipsoid A := by
  show _ ↔ _
  simp only [ellipsoid, Set.mem_ofPred_eq]
  rw [← quad_congr A B v.ofLp]

/-- `det (Bᵀ A B) = det(B)² det(A)`. -/
theorem det_congr (A B : Matrix (Fin n) (Fin n) ℝ) :
    (Bᵀ * A * B).det = B.det ^ 2 * A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- The congruence factor transports: `S' = B⁻¹ S` works for `A' = Bᵀ A B`. -/
theorem congr_factor {A S B : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ * A * S = 1)
    (hB : IsUnit B.det) :
    (B⁻¹ * S)ᵀ * (Bᵀ * A * B) * (B⁻¹ * S) = 1 := by
  have h1 : (B⁻¹)ᵀ * Bᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv B hB, Matrix.transpose_one]
  calc (B⁻¹ * S)ᵀ * (Bᵀ * A * B) * (B⁻¹ * S)
      = Sᵀ * ((B⁻¹)ᵀ * Bᵀ) * A * (B * B⁻¹) * S := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = Sᵀ * A * S := by
        rw [h1, Matrix.mul_nonsing_inv B hB]
        simp [Matrix.mul_assoc]
    _ = 1 := hS

/-- **H10 — the lattice transfer.**  If `E_A` contains no non-zero point of the lattice `B(ℤⁿ)`,
then the congruent ellipsoid `E_{BᵀAB}` contains no non-zero point of `ℤⁿ`.  This is
`ChainEllipsoid.klartag_of_chain`'s last conjunct. -/
theorem integerPoints_eq_zero {A B : Matrix (Fin n) (Fin n) ℝ} (_hB : B.det ≠ 0)
    (hfree : ∀ y : Fin n → ℤ, y ≠ 0 →
      (WithLp.toLp 2 (B *ᵥ (fun i => (y i : ℝ))) : EuclideanSpace ℝ (Fin n)) ∉ ellipsoid A) :
    {v ∈ ellipsoid (Bᵀ * A * B) | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  apply Set.Subset.antisymm
  · rintro v ⟨hv, hint⟩
    choose y hy using hint
    have hvy : v.ofLp = fun i => (y i : ℝ) := by funext i; exact (hy i).symm
    by_contra hne
    rw [Set.mem_singleton_iff] at hne
    have hy0 : y ≠ 0 := by
      intro hzero
      apply hne
      apply WithLp.ofLp_injective (p := 2)
      rw [hvy, hzero]
      funext i
      simp
    exact hfree y hy0 (by
      rw [← hvy]
      exact (mem_ellipsoid_congr A B v).1 hv)
  · intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact ⟨zero_mem_ellipsoid _, fun i => ⟨0, by simp⟩⟩

/-- **H10, packaged for `klartag_of_chain`.**  From an `L`-free ellipsoid in the lattice frame
(`L = B(ℤⁿ)`) to the hypothesis body of `ChainEllipsoid.klartag_of_chain` in the integer frame. -/
theorem chain_hyp_of_transfer {m : ℕ} {A S B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {c : ℝ}
    (hApos : 0 < A.det) (hS : Sᵀ * A * S = 1) (hB : B.det ≠ 0)
    (hfree : ∀ y : Fin (m + 1) → ℤ, y ≠ 0 →
      (WithLp.toLp 2 (B *ᵥ (fun i => (y i : ℝ))) : EuclideanSpace ℝ (Fin (m + 1)))
        ∉ ellipsoid A)
    (hdet : Real.sqrt (B.det ^ 2 * A.det) * (c * (m : ℝ) ^ 2)
      ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal) :
    ∃ A' S' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
      0 < A'.det ∧ S'ᵀ * A' * S' = 1 ∧
      Real.sqrt A'.det * (c * (m : ℝ) ^ 2)
        ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal ∧
      {v ∈ ellipsoid A' | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} := by
  refine ⟨Bᵀ * A * B, B⁻¹ * S, ?_, congr_factor hS (isUnit_iff_ne_zero.2 hB), ?_, ?_⟩
  · rw [det_congr]
    have : 0 < B.det ^ 2 := by positivity
    exact mul_pos this hApos
  · rw [det_congr]; exact hdet
  · exact integerPoints_eq_zero hB hfree

open Module
open Submodule

/-- **The basis matrix.**  Every `ℤ`-lattice of full rank in `Fin n → ℝ` is `B(ℤⁿ)` for an
invertible real matrix `B`.  Stated for an arbitrary lattice (rule 7), not for Construction A:
`D5.S3.Arith.Lattices.Klartag.Construction.ConstructionA.latR` carries the two instances, so this applies to it directly. -/
theorem exists_basisMatrix (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 ∧ |B.det| = ZLattice.covolume L ∧
      ∀ x : Fin n → ℝ, x ∈ L ↔ ∃ y : Fin n → ℤ, x = B *ᵥ (fun i => (y i : ℝ)) := by
  classical

  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = n := by
    have h1 : Module.finrank ℤ L = Module.finrank ℝ (Fin n → ℝ) := ZLattice.rank ℝ L
    have h2 : Module.finrank ℝ (Fin n → ℝ) = n := by simp
    have h3 := Module.finrank_eq_card_chooseBasisIndex ℤ L
    omega
  let e : Module.Free.ChooseBasisIndex ℤ L ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let b : Module.Basis (Fin n) ℤ L := (Module.Free.chooseBasis ℤ L).reindex e
  let bR : Module.Basis (Fin n) ℝ (Fin n → ℝ) := b.ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range (bR : Fin n → (Fin n → ℝ))) = L :=
    b.ofZLatticeBasis_span ℝ
  have hBentry : ∀ i j, ((Pi.basisFun ℝ (Fin n)).toMatrix bR) i j = bR j i := by
    intro i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  refine ⟨(Pi.basisFun ℝ (Fin n)).toMatrix bR, ?_, ?_, ?_⟩
  · have : Invertible ((Pi.basisFun ℝ (Fin n)).toMatrix bR) :=
      Module.Basis.invertibleToMatrix (Pi.basisFun ℝ (Fin n)) bR
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_invertible _)).ne_zero
  · rw [ZLattice.covolume_eq_det L b]
    congr 1
    rw [← Matrix.det_transpose]
    congr 1
    ext i j
    rw [Matrix.transpose_apply, hBentry]
    exact congrFun (b.ofZLatticeBasis_apply ℝ L i) j
  · intro x
    have hmv : ∀ y : Fin n → ℤ,
        ((Pi.basisFun ℝ (Fin n)).toMatrix bR) *ᵥ (fun i => (y i : ℝ))
          = ∑ j : Fin n, ((y j : ℝ)) • bR j := by
      intro y
      funext i
      simp only [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply,
        Pi.basisFun_repr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [← hspan]
    constructor
    · intro hx
      choose y hy using (bR.mem_span_iff_repr_mem ℤ x).1 hx
      refine ⟨y, ?_⟩
      rw [hmv]
      conv_lhs => rw [← bR.sum_repr x]
      exact Finset.sum_congr rfl (fun j _ => by rw [← hy j]; rfl)
    · rintro ⟨y, rfl⟩
      rw [hmv]
      refine Submodule.sum_mem _ (fun j _ => ?_)
      have : ((y j : ℝ)) • bR j = (y j) • bR j := by
        rw [← Int.cast_smul_eq_zsmul ℝ]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

end D5.S3.Arith.Lattices.Klartag.Construction.LatticeTransfer
