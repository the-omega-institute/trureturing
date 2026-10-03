/- GID: D5/S3/Arith/AbsoluteValues/Heights/MixedBall
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/MixedBall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The squared norm in the mixed space splits into real and complex place components. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.CubeSlicing
public import D5.S3.Arith.AbsoluteValues.Heights.NumberFieldLattice
public import Mathlib.Analysis.Matrix.LDL

public section

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K] (κ : Type*)

/-- The index type of the standard real coordinates of the euclidean tuple space. -/
abbrev mixedIndex : Type _ :=
  ({w : InfinitePlace K // IsReal w} × κ) ⊕ ({w : InfinitePlace K // IsComplex w} × (κ ⊕ κ))

/-- Standard real coordinates on the tuples of mixed-space points. -/
@[expose] def toMixedTuple : (mixedIndex K κ → ℝ) ≃ₗ[ℝ] (κ → mixedSpace K) where
  toFun c := fun j ↦ (fun w ↦ c (.inl (w, j)),
    fun w ↦ ⟨c (.inr (w, .inl j)), c (.inr (w, .inr j))⟩)
  invFun u := Sum.elim (fun p ↦ (u p.2).1 p.1)
    (fun q ↦ Sum.elim (fun j ↦ ((u j).2 q.1).re) (fun j ↦ ((u j).2 q.1).im) q.2)
  map_add' _ _ := rfl
  map_smul' r c := by
    ext j
    · rfl
    · simp [Complex.ext_iff, Complex.real_smul]
  left_inv c := by
    ext idx
    rcases idx with p | ⟨w, j | j⟩ <;> rfl
  right_inv u := by
    ext j
    · rfl
    · rfl

variable {K κ}

variable [Fintype κ]

open scoped Classical in
theorem inner_toMixedPi_toMixedTuple (c c' : mixedIndex K κ → ℝ) :
    inner ℝ (toMixedPi K κ (toMixedTuple K κ c)) (toMixedPi K κ (toMixedTuple K κ c'))
      = ∑ idx, c idx * c' idx := by
  have htrace (j : κ) :
      mixedTrace K (star ((toMixedTuple K κ c) j) * ((toMixedTuple K κ c') j))
        = (∑ w : {w : InfinitePlace K // IsReal w}, c (.inl (w, j)) * c' (.inl (w, j)))
          + ∑ w : {w : InfinitePlace K // IsComplex w},
              (c (.inr (w, .inl j)) * c' (.inr (w, .inl j))
                + c (.inr (w, .inr j)) * c' (.inr (w, .inr j))) := by
    simp only [mixedTrace, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    have h1 : (star ((toMixedTuple K κ) c j) * (toMixedTuple K κ) c' j).2 w
        = (starRingEnd ℂ) ⟨c (.inr (w, .inl j)), c (.inr (w, .inr j))⟩ *
          ⟨c' (.inr (w, .inl j)), c' (.inr (w, .inr j))⟩ := rfl
    rw [h1, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hinner (u v : κ → mixedSpace K) :
      inner ℝ (toMixedPi K κ u) (toMixedPi K κ v) =
        ∑ l, mixedTrace K (star (u l) * v l) := by
    have hEuclidean (a b : euclidean.mixedSpace K) :
        inner ℝ a b = mixedTrace K (star (euclidean.toMixed K a) *
          (euclidean.toMixed K b)) := by
      rw [show (inner ℝ a b : ℝ) = inner ℝ a.ofLp.1 b.ofLp.1 +
          inner ℝ a.ofLp.2 b.ofLp.2 from rfl, PiLp.inner_apply, PiLp.inner_apply]
      simp only [mixedTrace, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_mul, Prod.snd_mul,
        Pi.mul_apply, Prod.fst_star, Pi.star_apply, star_trivial, Prod.snd_star,
        Pi.star_apply, Complex.star_def, RCLike.inner_apply, Complex.inner, conj_trivial]
      congr 1
      · exact Finset.sum_congr rfl fun w _ ↦ by rw [mul_comm]; rfl
      · exact Finset.sum_congr rfl fun w _ ↦ by rw [mul_comm]; rfl
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [hEuclidean]
    congr 1
  rw [hinner]
  simp only [htrace]
  rw [Finset.sum_add_distrib, Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_prod_type]; exact Finset.sum_comm
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [Fintype.sum_sum_type, Finset.sum_add_distrib]

variable (K κ)

open scoped Classical in
/-- The standard real coordinates identify the euclidean tuple space with a euclidean space. -/
@[expose] noncomputable def mixedPiIsometry :
    EuclideanSpace ℝ (mixedIndex K κ) ≃ₗᵢ[ℝ] mixedPi K κ :=
  LinearEquiv.isometryOfInner
    (((WithLp.linearEquiv 2 ℝ (mixedIndex K κ → ℝ)).trans (toMixedTuple K κ)).trans
      (toMixedPi K κ))
    (fun x y ↦ by
      rw [show (((WithLp.linearEquiv 2 ℝ (mixedIndex K κ → ℝ)).trans (toMixedTuple K κ)).trans
            (toMixedPi K κ)) x
          = toMixedPi K κ (toMixedTuple K κ (WithLp.ofLp x)) from rfl,
        show (((WithLp.linearEquiv 2 ℝ (mixedIndex K κ → ℝ)).trans (toMixedTuple K κ)).trans
            (toMixedPi K κ)) y
          = toMixedPi K κ (toMixedTuple K κ (WithLp.ofLp y)) from rfl,
        inner_toMixedPi_toMixedTuple, PiLp.inner_apply]
      exact Finset.sum_congr rfl fun i _ ↦ by
        change WithLp.ofLp x i * WithLp.ofLp y i = inner ℝ (WithLp.ofLp x i) (WithLp.ofLp y i)
        rw [RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm])

end NumberField.mixedEmbedding

namespace MeasureTheory

end MeasureTheory

namespace MeasureTheory

open Metric

end MeasureTheory

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace
open scoped Pointwise

variable (K : Type*) [Field K] [NumberField K] (κ : Type*) [Fintype κ]

open scoped Classical in
/-- The tuple of coordinates of a point of the euclidean tuple space at a real place. -/
@[expose] noncomputable def realPart (w : {w : InfinitePlace K // IsReal w}) :
    mixedPi K κ →ₗ[ℝ] EuclideanSpace ℝ κ where
  toFun x := WithLp.toLp 2 (fun j ↦ (((toMixedPi K κ).symm x) j).1 w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
/-- The tuple of coordinates of a point of the euclidean tuple space at a complex place. -/
@[expose] noncomputable def complexPart (w : {w : InfinitePlace K // IsComplex w}) :
    mixedPi K κ →ₗ[ℝ] EuclideanSpace ℂ κ where
  toFun x := WithLp.toLp 2 (fun j ↦ (((toMixedPi K κ).symm x) j).2 w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {K κ}

open scoped Classical in
theorem norm_sq_mixedPi (x : mixedPi K κ) :
    ‖x‖ ^ 2 = (∑ w, ‖realPart K κ w x‖ ^ 2) + ∑ w, ‖complexPart K κ w x‖ ^ 2 := by
  obtain ⟨c, rfl⟩ := (mixedPiIsometry K κ).surjective x
  rw [(mixedPiIsometry K κ).norm_map]
  rw [show ‖c‖ ^ 2 = ∑ idx, (WithLp.ofLp c idx) ^ 2 by
    rw [← (fun a ↦ EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 a)) (WithLp.ofLp c), WithLp.toLp_ofLp]]
  change (∑ idx, (WithLp.ofLp c idx) ^ 2) =
    (∑ w, ‖(WithLp.toLp 2 (fun j : κ ↦ WithLp.ofLp c (.inl (w, j))) :
      EuclideanSpace ℝ κ)‖ ^ 2) +
    ∑ w, ‖(WithLp.toLp 2 (fun j : κ ↦
      (⟨WithLp.ofLp c (.inr (w, .inl j)),
        WithLp.ofLp c (.inr (w, .inr j))⟩ : ℂ)) : EuclideanSpace ℂ κ)‖ ^ 2
  simp only [(fun a : κ → ℝ ↦ EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 a))]
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_prod_type]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    let z : EuclideanSpace ℂ κ := WithLp.toLp 2 (fun j : κ ↦
      (⟨WithLp.ofLp c (.inr (w, .inl j)),
        WithLp.ofLp c (.inr (w, .inr j))⟩ : ℂ))
    change (∑ idx : κ ⊕ κ, (WithLp.ofLp c (.inr (w, idx))) ^ 2) = ‖z‖ ^ 2
    rw [EuclideanSpace.norm_sq_eq]
    simp only [z, PiLp.toLp_apply, Complex.sq_norm, Complex.normSq_mk]
    rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring

end NumberField.mixedEmbedding

namespace Matrix

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {k : ℕ} {ι : Type*} [Fintype ι]

end Matrix

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace Matrix

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] {k : ℕ}

end NumberField.mixedEmbedding

namespace NumberField.mixedEmbedding

open Module MeasureTheory NumberField NumberField.InfinitePlace Matrix

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] {k : ℕ}

end NumberField.mixedEmbedding
