/- GID: D5/S3/Quantum/Foundation/OriginalReturnSectors
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalReturnSectors
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Whole original return faces near an arbitrary interior source. -/

import D5.S3.Quantum.Foundation.SingleLabelNormalBody
import D5.S3.Quantum.Foundation.MixedExclusionGeometry
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Analysis.Normed.Affine.Convex

/-! Original full-cone positive normals and actual whole exclusion returns. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.OriginalReturnSectors

open Set Filter Topology
open scoped RealInnerProductSpace
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open OriginalFacePolarity ContinuousFrameSum SingleLabelNormalBody WholePairBallConfirmation

section RealSpectrum
open Module
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
private def rightFrame (L : X →L[ℝ] Y) : OrthonormalBasis (Fin (finrank ℝ X)) ℝ X :=
  L.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
private def leading (L : X →L[ℝ] Y) (k : ℕ) : Submodule ℝ X :=
  Submodule.span ℝ (rightFrame L '' {i | (i:ℕ)<k})
/- Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Authors: The Tau Ceti contributors; Jon Crall, Claude Fable 5, Claude Opus 4.8.
Released under Apache 2.0; full license: docs/reports/licenses/TauCeti-LICENSE.txt.
The real eigenbasis estimates below adapt the leaf declarations
OrthonormalBasis.repr_apply_of_eigenbasis,
LinearMap.re_inner_apply_self_eq_sum_of_eigenbasis,
LinearMap.le_re_inner_of_eigenbasis and LinearMap.re_inner_le_of_eigenbasis
from TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9,
Analysis/InnerProductSpace/Orthonormal/Coordinates.lean and CourantFischer.lean.
Selected-span notation is expanded to native Submodule.span; real parts are
identities over ℝ. Retire these private leaf adaptations when this repository's
pinned mathlib provides the equivalent declarations, and directly apply them.
-/
omit [FiniteDimensional ℝ X] in
private theorem repr_apply_of_eigenbasis
    (b : OrthonormalBasis (Fin (finrank ℝ X)) ℝ X) (S : X →ₗ[ℝ] X)
    {μ : Fin (finrank ℝ X) → ℝ} (hb : ∀ i, S (b i) = μ i • b i)
    (x : X) (i : Fin (finrank ℝ X)) :
    b.repr (S x) i = μ i * b.repr x i := by
  classical
  conv_lhs => rw [← b.sum_repr x]
  simp [map_sum,hb,smul_smul,mul_comm,Pi.single_apply]

omit [FiniteDimensional ℝ X] in
private theorem inner_apply_self_eq_sum_of_eigenbasis
    (S : X →ₗ[ℝ] X) (w : OrthonormalBasis (Fin (finrank ℝ X)) ℝ X)
    {μ : Fin (finrank ℝ X) → ℝ} (hw : ∀ i, S (w i) = μ i • w i) (x : X) :
    ⟪S x,x⟫ = ∑ i, μ i * ‖w.repr x i‖^2 := by
  rw [← w.repr.inner_map_map (S x) x,PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply,repr_apply_of_eigenbasis w S hw x i]
  simp only [conj_trivial,Real.norm_eq_abs,sq_abs]
  ring

private theorem norm_square (L : X →L[ℝ] Y) (x : X) :
    ‖L x‖^2 = ∑ i : Fin (finrank ℝ X), L.toLinearMap.singularValues i ^ 2 *
      ‖(rightFrame L).repr x i‖^2 := by
  have hT := L.toLinearMap.isSymmetric_adjoint_comp_self
  have h := inner_apply_self_eq_sum_of_eigenbasis
    (L.toLinearMap.adjoint.comp L.toLinearMap) (rightFrame L)
    (hT.apply_eigenvectorBasis rfl) x
  rw [LinearMap.comp_apply,LinearMap.adjoint_inner_left,real_inner_self_eq_norm_sq] at h
  simpa [LinearMap.sq_singularValues_fin,hT] using h
omit [FiniteDimensional ℝ X] in
private theorem coeff_zero_of_span (b : OrthonormalBasis (Fin (finrank ℝ X)) ℝ X)
    {s : Set (Fin (finrank ℝ X))} {x : X} (hx : x ∈ Submodule.span ℝ (b '' s))
    {i : Fin (finrank ℝ X)} (hi : i ∉ s) : b.repr x i = 0 := by
  have hs := b.toBasis.repr_support_subset_of_mem_span s (by simpa using hx)
  have hn : i ∉ (b.toBasis.repr x).support := fun h => hi (hs h)
  simpa using Finsupp.notMem_support_iff.mp hn
private theorem frame_sum_sq (L : X →L[ℝ] Y) (x : X) :
    ∑ i : Fin (finrank ℝ X), ‖(rightFrame L).repr x i‖^2 = ‖x‖^2 := by
  simp_rw [(rightFrame L).repr_apply_apply]
  exact (rightFrame L).sum_sq_norm_inner_right x
private theorem leading_dimension (L : X →L[ℝ] Y) {k : ℕ} (hk : k ≤ finrank ℝ X) :
    finrank ℝ (leading L k) = k := by
  have h := finrank_span_eq_card ((rightFrame L).orthonormal.linearIndependent.comp
    (fun i : {i : Fin (finrank ℝ X) // (i:ℕ)<k} => (i:Fin (finrank ℝ X))) Subtype.val_injective)
  have hd : finrank ℝ (leading L k) = Fintype.card {i : Fin (finrank ℝ X) // (i:ℕ)<k} := by
    unfold leading
    rw [Set.image_eq_range]
    convert h using 1; rfl
  rw [hd]
  let e : {i : Fin (finrank ℝ X) // (i:ℕ)<k} ≃ Fin k :=
    { toFun := fun i => ⟨i.val.val,i.property⟩
      invFun := fun i => ⟨⟨i.val,i.isLt.trans_le hk⟩,i.isLt⟩
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin k)
private theorem le_inner_of_eigenbasis
    (S : X →ₗ[ℝ] X) (w : OrthonormalBasis (Fin (finrank ℝ X)) ℝ X)
    {μ : Fin (finrank ℝ X) → ℝ} (hw : ∀ i, S (w i) = μ i • w i)
    {s : Set (Fin (finrank ℝ X))} {c : ℝ} (hc : ∀ i ∈ s, c ≤ μ i)
    {x : X} (hx : x ∈ Submodule.span ℝ (w '' s)) :
    c*‖x‖^2 ≤ ⟪S x,x⟫ := by
  rw [inner_apply_self_eq_sum_of_eigenbasis S w hw x,
    show c*‖x‖^2 = ∑ i, c*‖w.repr x i‖^2 by
      rw [← Finset.mul_sum]; congr 1; simpa only [w.repr_apply_apply] using (w.sum_sq_norm_inner_right x).symm]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [coeff_zero_of_span w hx hp]; simp

private theorem inner_le_of_eigenbasis
    (S : X →ₗ[ℝ] X) (w : OrthonormalBasis (Fin (finrank ℝ X)) ℝ X)
    {μ : Fin (finrank ℝ X) → ℝ} (hw : ∀ i, S (w i) = μ i • w i)
    {s : Set (Fin (finrank ℝ X))} {c : ℝ} (hc : ∀ i ∈ s, μ i ≤ c)
    {x : X} (hx : x ∈ Submodule.span ℝ (w '' s)) :
    ⟪S x,x⟫ ≤ c*‖x‖^2 := by
  rw [inner_apply_self_eq_sum_of_eigenbasis S w hw x,
    show c*‖x‖^2 = ∑ i, c*‖w.repr x i‖^2 by
      rw [← Finset.mul_sum]; congr 1; simpa only [w.repr_apply_apply] using (w.sum_sq_norm_inner_right x).symm]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [coeff_zero_of_span w hx hp]; simp

private theorem tail_bound (L : X →L[ℝ] Y) {k : ℕ} (_hk : k < finrank ℝ X)
    {x : X} (hx : x ∈ (leading L k)ᗮ) :
    ‖L x‖ ≤ L.toLinearMap.singularValues k * ‖x‖ := by
  have hxspan : x ∈ Submodule.span ℝ (rightFrame L '' {i | k ≤ (i:ℕ)}) := by
    rw [← (rightFrame L).sum_repr x]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : k ≤ (i:ℕ)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩)
    · have hm : rightFrame L i ∈ leading L k := Submodule.subset_span ⟨i,Nat.lt_of_not_ge hi,rfl⟩
      have hz : (rightFrame L).repr x i = 0 := by
        rw [(rightFrame L).repr_apply_apply]
        exact (Submodule.mem_orthogonal _ _).mp hx _ hm
      rw [hz,zero_smul]; exact Submodule.zero_mem _
  have hs := inner_le_of_eigenbasis (L.toLinearMap.adjoint.comp L.toLinearMap)
    (rightFrame L) (L.toLinearMap.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl)
    (c := L.toLinearMap.singularValues k^2) (fun i (hi : k ≤ (i:ℕ)) => by
      rw [← L.toLinearMap.sq_singularValues_fin rfl i]
      exact pow_le_pow_left₀ (L.toLinearMap.singularValues_nonneg _)
        (L.toLinearMap.singularValues_antitone hi) 2) hxspan
  rw [LinearMap.comp_apply,LinearMap.adjoint_inner_left,real_inner_self_eq_norm_sq] at hs
  change ‖L x‖^2 ≤ L.toLinearMap.singularValues k^2*‖x‖^2 at hs
  apply le_of_sq_le_sq _ (mul_nonneg (L.toLinearMap.singularValues_nonneg _) (norm_nonneg x))
  nlinarith

private theorem prefix_bound (L : X →L[ℝ] Y) {k : ℕ} (_hk : k < finrank ℝ X)
    {x : X} (hx : x ∈ leading L (k+1)) :
    L.toLinearMap.singularValues k * ‖x‖ ≤ ‖L x‖ := by
  have hs := le_inner_of_eigenbasis (L.toLinearMap.adjoint.comp L.toLinearMap)
    (rightFrame L) (L.toLinearMap.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl)
    (c := L.toLinearMap.singularValues k^2) (fun i (hi : (i:ℕ)<k+1) => by
      rw [← L.toLinearMap.sq_singularValues_fin rfl i]
      exact pow_le_pow_left₀ (L.toLinearMap.singularValues_nonneg _)
        (L.toLinearMap.singularValues_antitone (by omega)) 2) hx
  rw [LinearMap.comp_apply,LinearMap.adjoint_inner_left,real_inner_self_eq_norm_sq] at hs
  change L.toLinearMap.singularValues k^2*‖x‖^2 ≤ ‖L x‖^2 at hs
  apply le_of_sq_le_sq _ (norm_nonneg _)
  nlinarith

private theorem leading_projection_bound (L : X →L[ℝ] Y) {k : ℕ}
    (hk : 0 < k) (_hkd : k ≤ finrank ℝ X) (x : X) :
    L.toLinearMap.singularValues (k-1) * ‖(leading L k).starProjection x‖ ≤ ‖L x‖ := by
  let P := (leading L k).starProjection
  have hs : L.toLinearMap.singularValues (k-1)^2 * ‖P x‖^2 ≤ ‖L x‖^2 := by
    rw [norm_square L x,← frame_sum_sq L (P x),Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : (i:ℕ)<k
    · have hm : rightFrame L i ∈ leading L k := Submodule.subset_span ⟨i,hi,rfl⟩
      have hcoeff : (rightFrame L).repr (P x) i = (rightFrame L).repr x i := by
        simp only [(rightFrame L).repr_apply_apply]
        have hh := (leading L k).starProjection_inner_eq_zero x (rightFrame L i) hm
        rw [inner_sub_left] at hh
        have hh' := sub_eq_zero.mp hh
        calc
          ⟪rightFrame L i,P x⟫ = ⟪P x,rightFrame L i⟫ := real_inner_comm _ _
          _ = ⟪x,rightFrame L i⟫ := hh'.symm
          _ = ⟪rightFrame L i,x⟫ := real_inner_comm _ _
      rw [hcoeff]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (L.toLinearMap.singularValues_nonneg _)
          (L.toLinearMap.singularValues_antitone (by omega)) 2) (sq_nonneg _)
    · have hz := coeff_zero_of_span (rightFrame L)
        ((leading L k).starProjection_apply_mem x) hi
      rw [hz]
      simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero]
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  apply le_of_sq_le_sq _ (norm_nonneg _)
  nlinarith

private theorem thin_of_projected_error (L : X →L[ℝ] Y) (U : Submodule ℝ Y)
    {k : ℕ} (hU : finrank ℝ U = k) (hk : k < finrank ℝ X)
    {α : ℝ} (_hα : 0 ≤ α) (herr : ∀ x, ‖Uᗮ.starProjection (L x)‖ ≤ α*‖x‖) :
    L.toLinearMap.singularValues k ≤ α := by
  let A := U.orthogonalProjectionOnto.toLinearMap.comp L.toLinearMap
  have hsum := A.finrank_range_add_finrank_ker
  have hrange : finrank ℝ A.range ≤ k := by rw [← hU]; exact A.range.finrank_le
  have hlead := leading_dimension L (Nat.succ_le_of_lt hk)
  simp only [Nat.succ_eq_add_one] at hlead
  have hnot : leading L (k+1) ⊓ A.ker ≠ ⊥ := by
    intro hh
    have hle := Submodule.finrank_add_finrank_le_of_disjoint (disjoint_iff.mpr hh)
    omega
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnot
  have hpref := prefix_bound L hk hx.1
  have hAx : U.starProjection (L x) = 0 := by
    have hh := hx.2
    change A x = 0 at hh
    exact congrArg (fun v : U => (v:Y)) hh
  have hdecomp := U.starProjection_add_starProjection_orthogonal (L x)
  rw [hAx,zero_add] at hdecomp
  have hh := herr x
  rw [hdecomp] at hh
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  nlinarith

private theorem kept_of_dual_coercive (L : X →L[ℝ] Y) (U : Submodule ℝ Y)
    {k : ℕ} (hU : finrank ℝ U = k) (hk : 0 < k) (hkd : k ≤ finrank ℝ X)
    {β : ℝ} (_hβ : 0 < β)
    (hcoercive : ∀ h ∈ U, β*‖h‖ ≤ ‖L.adjoint h‖) :
    β ≤ L.toLinearMap.singularValues (k-1) := by
  let P := leading L (k-1)
  let Q := P.map L.toLinearMap
  have hQdim : finrank ℝ Q ≤ k-1 :=
    (Submodule.finrank_map_le _ _).trans_eq (leading_dimension L (by omega))
  have hnot : U ⊓ Qᗮ ≠ ⊥ := by
    intro hh
    have hle := Submodule.finrank_add_finrank_le_of_disjoint (disjoint_iff.mpr hh)
    have hsum := Q.finrank_add_finrank_orthogonal
    omega
  obtain ⟨h,hh,hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnot
  have hadj : L.adjoint h ∈ Pᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact (Submodule.mem_orthogonal _ _).mp hh.2 (L x) ⟨x,hx,rfl⟩
  have htail := tail_bound L (by omega : k-1 < finrank ℝ X) hadj
  have hcs := real_inner_le_norm h (L (L.adjoint h))
  rw [← ContinuousLinearMap.adjoint_inner_left,real_inner_self_eq_norm_sq] at hcs
  have hbound : ‖L.adjoint h‖ ≤ L.toLinearMap.singularValues (k-1)*‖h‖ := by
    by_cases hz : L.adjoint h = 0
    · simpa only [hz,norm_zero] using mul_nonneg (L.toLinearMap.singularValues_nonneg (k-1)) (norm_nonneg h)
    have hn := norm_pos_iff.mpr hz
    have hm := mul_le_mul_of_nonneg_left htail (norm_nonneg h)
    nlinarith
  have hc := hcoercive h hh.1
  have hn := norm_pos_iff.mpr hh0
  nlinarith

/-- Span of the ordered right singular directions with zero-based index at least k.
The native sorted eigenbasis chooses an orthonormal frame within tied eigenspaces. -/
def singularTail (L : X →L[ℝ] Y) (k : ℕ) : Submodule ℝ X :=
  Submodule.span ℝ (rightFrame L '' {i | k ≤ (i:ℕ)})

private theorem singularTail_eq (L : X →L[ℝ] Y) (k : ℕ) :
    singularTail L k = (leading L k)ᗮ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change k ≤ (i:ℕ) at hi
    change rightFrame L i ∈ (leading L k)ᗮ
    apply (Submodule.mem_orthogonal _ _).mpr
    intro x hx
    have hz := coeff_zero_of_span (rightFrame L) hx
      (show i ∉ {j : Fin (finrank ℝ X) | (j:ℕ)<k} from by intro hj; exact Nat.not_lt_of_ge hi hj)
    rw [(rightFrame L).repr_apply_apply] at hz
    exact (real_inner_comm _ _).trans hz
  · intro x hx
    rw [← (rightFrame L).sum_repr x]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : k ≤ (i:ℕ)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩)
    · have hm : rightFrame L i ∈ leading L k := Submodule.subset_span ⟨i,(show (i:ℕ)<k from Nat.lt_of_not_ge hi),rfl⟩
      have hz : (rightFrame L).repr x i = 0 := by
        rw [(rightFrame L).repr_apply_apply]
        exact (Submodule.mem_orthogonal _ _).mp hx _ hm
      rw [hz,zero_smul]
      exact Submodule.zero_mem _

private theorem singular_le_norm (L : X →L[ℝ] Y) (i : ℕ) :
    L.toLinearMap.singularValues i ≤ ‖L‖ := by
  by_cases hi : i < finrank ℝ X
  · have hp := prefix_bound L hi (Submodule.subset_span
      (show rightFrame L ⟨i,hi⟩ ∈ rightFrame L '' {j | (j:ℕ) < (i+1)} from ⟨⟨i,hi⟩,by simp,rfl⟩))
    have hn : ‖rightFrame L ⟨i,hi⟩‖ = 1 := (rightFrame L).norm_eq_one _
    rw [hn,mul_one] at hp
    exact hp.trans (by simpa [hn] using L.le_opNorm (rightFrame L ⟨i,hi⟩))
  · rw [L.toLinearMap.singularValues_of_finrank_le (Nat.le_of_not_gt hi)]
    exact norm_nonneg _

end RealSpectrum

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- The maximum distance from the entire return face to the fixed source face. -/
def leakage (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p t : V) : ℝ :=
  sSup ((fun x => Metric.infDist x (exclusion C u p)) '' exclusion C u t)

private theorem zero_on_source (p : pure C u) (a : ExclusionChart C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (e : V →L[ℝ] ℝ) (he : ∀ x ∈ C, 0 ≤ e x) (hey : e y = 0) :
    ∀ x ∈ exclusion C u p, e x = 0 := by
  rw [MixedExclusionGeometry.chart_intrinsic p a] at hy
  obtain ⟨ξ, hξ, rfl⟩ := hy
  have hξ1 : ‖ξ‖ < 1 := by simpa using hξ
  have hbound : ‖slope a e‖ ≤ e (a.param 0) := affine_nonneg_bound (fun z hz => by
    rw [← slope_formula]
    exact he _ (a.whole ▸ mem_image_of_mem a.param (by simpa using hz)).1.1)
  have hcs := real_inner_le_norm (-(slope a e)) ξ
  rw [inner_neg_left, norm_neg] at hcs
  rw [slope_formula] at hey
  have hn : ‖slope a e‖ = 0 := by
    nlinarith [norm_nonneg (slope a e)]
  have hz := norm_eq_zero.mp hn
  intro x hx
  obtain ⟨z, _, rfl⟩ := a.whole.symm ▸ hx
  rw [slope_formula, hz, inner_zero_left, add_zero]
  simpa only [hz, inner_zero_left, add_zero] using hey

private theorem zero_face_eq (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) {y t : V}
    (hy : y ∈ intrinsicInterior ℝ (exclusion C u p)) (ht : t ∈ base C u)
    (e : V →L[ℝ] ℝ) (he : e ∈ effects C u) (hey : e y = 0) (het : e t = 1) :
    {x | x ∈ base C u ∧ e x = 0} = exclusion C u p := by
  let G := {x | x ∈ base C u ∧ e x = 0}
  have all := exclusion_ball_faces hc hs hg hB
  obtain ⟨a⟩ := hB p
  have hFG : exclusion C u p ⊆ G := fun x hx =>
    ⟨hx.1, zero_on_source p a hy e (fun z hz => (he z hz).1) hey x hx⟩
  have hGconv : Convex ℝ G := by
    intro x hx z hz a b ha hb hab
    refine ⟨base_convex C u hx.1 hz.1 ha hb hab, ?_⟩
    simp [map_add, map_smul, hx.2, hz.2]
  have hGexp : IsExposed ℝ (base C u) G := by
    intro _
    refine ⟨-e, ?_⟩
    ext x
    constructor
    · rintro ⟨hx, hx0⟩
      exact ⟨hx, fun z hz => by simpa [hx0] using (he z hz.1).1⟩
    · rintro ⟨hx, hmax⟩
      have hh := hmax y ((intrinsicInterior_subset hy).1)
      change -e y ≤ -e x at hh
      rw [hey] at hh
      exact ⟨hx, le_antisymm (by simpa only [neg_zero, neg_nonneg] using hh)
        (he x hx.1).1⟩
  have hproper : G ≠ base C u := by
    intro heq
    have hh : t ∈ G := heq.symm ▸ ht
    linarith [hh.2]
  rcases all.2.1 G ⟨y, hFG (intrinsicInterior_subset hy)⟩ hGconv hGexp.isExtreme
      hproper with ⟨q, hq⟩ | ⟨q, hq⟩
  · exact ((all.1 p).1.not_subsingleton (fun x hx z hz => by
      have hxq := hq ▸ hFG hx
      have hzq := hq ▸ hFG hz
      exact hxq.trans hzq.symm)).elim
  · obtain ⟨b⟩ := hB q
    have hsub : exclusion C u p ⊆ exclusion C u q := hq ▸ hFG
    have hface := (all.1 p).2.2.2.2.1.mono (all.1 q).2.2.2.2.1.subset hsub
    exact hq.trans (chart_face_eq b (all.1 p).2.2.1 hface (all.1 p).1).symm

/-- Every whole actual return lies uniformly close to F as its returned pure
point approaches any relative-interior point of F. The label limit may be mixed. -/
private theorem whole_return_near_source (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r t : pure C u,
      dist (r : V) y < ε → (t : V) ∈ exclusion C u r →
      ∀ x ∈ exclusion C u t, Metric.infDist x (exclusion C u p) < δ := by
  classical
  by_contra! hn
  have hb (n : ℕ) := hn (1 / ((n : ℝ) + 1)) (by positivity)
  choose r t hr ht x hx hfar using hb
  let e (n : ℕ) : V →L[ℝ] ℝ :=
    (((exclusion_ball_faces hc hs hg hB).1 (t n)).2.2.2.2.2.2.choose).toContinuousLinearMap
  have he (n : ℕ) : confirms C u (t n) (e n).toLinearMap :=
    ((exclusion_ball_faces hc hs hg hB).1 (t n)).2.2.2.2.2.2.choose_spec.1
  have hezero (n : ℕ) (z : V) (hz : z ∈ exclusion C u (t n)) : e n z = 0 := by
    have hh := ((exclusion_ball_faces hc hs hg hB).1 (t n)).2.2.2.2.2.2.choose_spec.2
    exact (hh ▸ hz).2
  have hrconv : Tendsto (fun n => (r n : V)) atTop (𝓝 y) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => (show ‖(r n : V) - y‖ < 1 / ((n : ℝ) + 1) from
        by simpa [dist_eq_norm] using hr n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hK := base_compact hc hs
  obtain ⟨z, hz, φ, hφ, hlim⟩ := (hK.prod (hK.prod (effects_compact hs hg))).tendsto_subseq
    (fun n => show ((t n : V), x n, e n) ∈
      base C u ×ˢ (base C u ×ˢ effects C u) from
      ⟨pure_mem (t n), (hx n).1, (he n).1⟩)
  have htl := hlim.fst_nhds
  have hxl := hlim.snd_nhds.fst_nhds
  have hel := hlim.snd_nhds.snd_nhds
  have hrl := hrconv.comp hφ.tendsto_atTop
  have hev : Continuous (fun v : (V →L[ℝ] ℝ) × V => v.1 v.2) := by fun_prop
  have hey : z.2.2 y = 0 := by
    apply tendsto_nhds_unique ((hev.tendsto _).comp (hel.prodMk_nhds hrl))
    convert tendsto_const_nhds (x := (0 : ℝ)) using 1
    ext n
    exact hezero (φ n) _ ((exclusion_symmetric (r (φ n)) (t (φ n))).mp (ht (φ n)))
  have hex : z.2.2 z.2.1 = 0 := by
    apply tendsto_nhds_unique ((hev.tendsto _).comp (hel.prodMk_nhds hxl))
    convert tendsto_const_nhds (x := (0 : ℝ)) using 1
    ext n
    exact hezero (φ n) _ (hx (φ n))
  have het : z.2.2 z.1 = 1 := by
    apply tendsto_nhds_unique ((hev.tendsto _).comp (hel.prodMk_nhds htl))
    convert tendsto_const_nhds (x := (1 : ℝ)) using 1
    ext n
    exact (he (φ n)).2
  have hxF : z.2.1 ∈ exclusion C u p :=
    zero_face_eq hc hs hg hB p hy hz.1 z.2.2 hz.2.2 hey het ▸ ⟨hz.2.1, hex⟩
  have hnear := Metric.tendsto_nhds.mp hxl δ hδ
  obtain ⟨n, hn⟩ := hnear.exists
  exact (hfar (φ n)).not_gt ((Metric.infDist_le_dist_of_mem hxF).trans_lt hn)

/-- Q133.7 with the actual attained maximum over the entire original return.
The constants precede both pure points; neither label injectivity nor purity
of any limiting label is required. -/
theorem whole_return_leakage (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r t : pure C u,
      dist (r : V) y < ε → (t : V) ∈ exclusion C u r → leakage C u p t < δ := by
  obtain ⟨ε, hε, h⟩ := whole_return_near_source hc hs hg hB p hy hδ
  refine ⟨ε, hε, fun r t hr ht => ?_⟩
  have hD := (exclusion_ball_faces hc hs hg hB).1 t
  exact (hD.2.1.sSup_lt_iff_of_continuous hD.1.nonempty
    (Metric.continuous_infDist_pt _).continuousOn δ).mpr (h r t hr ht)

private theorem radial_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ξ v : E} (hξ : ‖ξ‖ < 1) (hv : v ≠ ξ) :
    ∃ s : ℝ, 0 < s ∧ ‖ξ + s • (v - ξ)‖ = 1 := by
  have hd : 0 < ‖v - ξ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hv)
  let T := (2 + ‖ξ‖) / ‖v - ξ‖
  have hT : 0 < T := by dsimp [T]; positivity
  have hlarge : 1 ≤ ‖ξ + T • (v - ξ)‖ := by
    have hh := norm_sub_le (ξ + T • (v - ξ)) ξ
    have he : ξ + T • (v - ξ) - ξ = T • (v - ξ) := by abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hT] at hh
    have hmul : T * ‖v - ξ‖ = 2 + ‖ξ‖ := div_mul_cancel₀ _ hd.ne'
    linarith
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc hT.le
    (show ContinuousOn (fun s : ℝ => ‖ξ + s • (v - ξ)‖) (Icc 0 T) by fun_prop)
    (show (1 : ℝ) ∈ Icc ‖ξ + (0 : ℝ) • (v - ξ)‖ ‖ξ + T • (v - ξ)‖ from
      ⟨by simpa using hξ.le, hlarge⟩)
  refine ⟨s, lt_of_le_of_ne hs.1 ?_, he⟩
  intro hz
  have : ‖ξ‖ = 1 := by simpa [← hz] using he
  linarith

private theorem sphere_affine_basis {d : ℕ} (hd : 0 < d)
    {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ‖ξ‖ < 1) :
    ∃ b : AffineBasis (Fin (d + 1)) ℝ (EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖b i‖ = 1) ∧ ∀ i, 0 < b.coord i ξ := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  obtain ⟨b, hb, _⟩ := exists_mem_interior_convexHull_affineBasis
    (s := Metric.ball (0 : E) 1) (Metric.isOpen_ball.mem_nhds (by simpa using hξ))
  have hcoord : ∀ i, 0 < b.coord i ξ := by
    simpa only [b.interior_convexHull, mem_ofPred_eq] using hb
  have : Nontrivial (Fin (Module.finrank ℝ E + 1)) :=
    Fin.nontrivial_iff_two_le.mpr (by simpa [E] using Nat.succ_le_succ hd)
  have hne (i) : b i ≠ ξ := by
    obtain ⟨j, hj⟩ := exists_ne i
    intro he
    have hh := hcoord j
    rw [← he, b.coord_apply_ne hj] at hh
    exact lt_irrefl _ hh
  choose t ht hunit using fun i => radial_sphere hξ (hne i)
  let q := fun i => ξ + t i • (b i - ξ)
  let S := ∑ i, b.coord i ξ / t i
  have hS : 0 < S := Finset.sum_pos (fun i _ => div_pos (hcoord i) (ht i))
    Finset.univ_nonempty
  let w := fun i => (b.coord i ξ / t i) / S
  have hwpos (i) : 0 < w i := div_pos (div_pos (hcoord i) (ht i)) hS
  have hwsum : ∑ i, w i = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    exact div_self hS.ne'
  have hcomb : ∑ i, w i • q i = ξ := by
    simp only [q, smul_add, smul_smul, Finset.sum_add_distrib, ← Finset.sum_smul,
      hwsum, one_smul]
    have hwt (i) : w i * t i = S⁻¹ * b.coord i ξ := by
      dsimp [w]
      field_simp [(ht i).ne', hS.ne']
    simp_rw [hwt, mul_smul, ← Finset.smul_sum, smul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [b.linear_combination_coord_eq_self, b.sum_coord_apply_eq_one, one_smul,
      sub_self, smul_zero, add_zero]
  have hξspan : ξ ∈ affineSpan ℝ (range q) := by
    rw [← hcomb, ← Finset.univ.affineCombination_eq_linear_combination _ _ hwsum]
    exact affineCombination_mem_affineSpan hwsum q
  have hspan : affineSpan ℝ (range q) = ⊤ := by
    apply top_unique
    rw [← b.tot]
    apply affineSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    have hq := subset_affineSpan ℝ (range q) (mem_range_self i)
    have hh := AffineMap.lineMap_mem ((t i)⁻¹) hξspan hq
    convert hh using 1;
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, q,
        add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ht i).ne', one_smul,
        sub_add_cancel]
    rfl
  have hind : AffineIndependent ℝ q := by
    apply (affineIndependent_iff_finrank_vectorSpan_eq ℝ q (Fintype.card_fin _)).mpr
    rw [← direction_affineSpan, hspan, AffineSubspace.direction_top, finrank_top]
  let c : AffineBasis _ ℝ E := ⟨q, hind, hspan⟩
  have hccoord (i) : c.coord i ξ = w i := by
    rw [← hcomb, ← Finset.univ.affineCombination_eq_linear_combination _ _ hwsum]
    exact c.coord_apply_combination_of_mem (Finset.mem_univ i) hwsum
  have he : Module.finrank ℝ E = d := by simp [E]
  refine ⟨c.reindex (finCongr (congrArg (fun n => n + 1) he)), ?_, ?_⟩
  · intro i
    exact hunit _
  · intro i
    rw [AffineBasis.coord_reindex, hccoord]
    exact hwpos _


section SimplexStability
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

private def interpLinear (b : AffineBasis ι ℝ E) (x : ι → E) : E →L[ℝ] E :=
  ∑ i, (b.coord i).linear.toContinuousLinearMap.smulRight (x i)

private def interpConst (b : AffineBasis ι ℝ E) (x : ι → E) : E :=
  ∑ i, b.coord i 0 • x i

private theorem interp_formula (b : AffineBasis ι ℝ E) (x : ι → E) (z : E) :
    ∑ i, b.coord i z • x i = interpLinear b x z + interpConst b x := by
  have h (i) : b.coord i z = (b.coord i).linear z + b.coord i 0 := by
    simpa using (b.coord i).map_vadd (0 : E) z
  simp only [h, add_smul, Finset.sum_add_distrib, interpLinear, interpConst,
    sum_apply, ContinuousLinearMap.smulRight_apply,
    LinearMap.coe_toContinuousLinearMap']

private theorem interp_self (b : AffineBasis ι ℝ E) :
    interpLinear b b = 1 ∧ interpConst b b = 0 := by
  have hc : interpConst b b = 0 := b.linear_combination_coord_eq_self 0
  refine ⟨?_, hc⟩
  ext z
  have hh := interp_formula b b z
  rw [b.linear_combination_coord_eq_self, hc, add_zero] at hh
  exact hh.symm

private theorem interpLinear_continuous (b : AffineBasis ι ℝ E) :
    Continuous (interpLinear b) := by
  apply continuous_finsetSum
  intro i _
  exact ((ContinuousLinearMap.smulRightₗ (T := ℝ)
    (b.coord i).linear.toContinuousLinearMap : E →ₗ[ℝ] (E →L[ℝ] E)).continuous_of_finiteDimensional).comp
      (continuous_apply i)

omit [FiniteDimensional ℝ E] in
private theorem interpConst_continuous (b : AffineBasis ι ℝ E) :
    Continuous (interpConst b) := by
  unfold interpConst
  fun_prop

private theorem simplex_reconstruction (b : AffineBasis ι ℝ E) {y : E}
    (hy : ∀ i, 0 < b.coord i y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ι → E) (z : E),
      (∀ i, dist (x i) (b i) < δ) → dist z y < δ →
      AffineIndependent ℝ x ∧ ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
        ∑ i, w i • x i = z := by
  classical
  let L := interpLinear b
  let c := interpConst b
  have hL := interpLinear_continuous b
  have hc := interpConst_continuous b
  have hLb : L b = 1 := (interp_self b).1
  have hcb : c b = 0 := (interp_self b).2
  let h := fun p : (ι → E) × E => Ring.inverse (L p.1) (p.2 - c p.1)
  have hcont : ContinuousAt h (b, y) := by
    have hinv : ContinuousAt Ring.inverse (L b) := by
      simpa only [hLb, Units.val_one] using
        (NormedRing.inverse_continuousAt (1 : (E →L[ℝ] E)ˣ))
    have hi : ContinuousAt (fun p : (ι → E) × E => Ring.inverse (L p.1)) (b,y) := by
      have hi' : ContinuousAt Ring.inverse ((fun p : (ι → E) × E => L p.1) (b,y)) := hinv
      exact ContinuousAt.comp (f := fun p : (ι → E) × E => L p.1) (x := (b,y)) hi'
        ((hL.comp continuous_fst).continuousAt)
    exact hi.clm_apply ((continuous_snd.sub (hc.comp continuous_fst)).continuousAt)
  have hby : h (b,y) = y := by simp [h, hLb, hcb]
  have hevent : ∀ᶠ p : (ι → E) × E in 𝓝 (b,y),
      IsUnit (L p.1) ∧ (∀ i, 0 < b.coord i (h p)) ∧ AffineIndependent ℝ p.1 := by
    have hunit : ∀ᶠ p : (ι → E) × E in 𝓝 (b,y), IsUnit (L p.1) := by
      apply (Units.isOpen.preimage (hL.comp continuous_fst)).mem_nhds
      change IsUnit (L b)
      rw [hLb]
      exact isUnit_one
    apply hunit.and
    apply Filter.Eventually.and ?_ ?_
    · apply (eventually_all.mpr fun i => ?_)
      have ht := ((b.coord i).continuous_of_finiteDimensional.continuousAt.comp hcont)
      exact ht.eventually (lt_mem_nhds (by simpa only [Function.comp_apply, hby] using hy i))
    · exact (isOpen_setOfPred_affineIndependent.preimage continuous_fst).mem_nhds b.ind
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨δ,hδ, fun x z hx hz => ?_⟩
  have hp : dist (x,z) (b,y) < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨(dist_pi_lt_iff hδ).mpr hx,hz⟩
  obtain ⟨hunit, hpos, hind⟩ := hball hp
  refine ⟨hind, fun i => b.coord i (h (x,z)), hpos, b.sum_coord_apply_eq_one _, ?_⟩
  rw [interp_formula]
  change L x (Ring.inverse (L x) (z - c x)) + c x = z
  have hh := congrArg (fun f : E →L[ℝ] E => f (z-c x)) (Ring.mul_inverse_cancel (L x) hunit)
  change L x (Ring.inverse (L x) (z-c x)) = z-c x at hh
  rw [hh, sub_add_cancel]


private theorem fixed_simplex_ball (b : AffineBasis ι ℝ E) {y : E}
    (hy : ∀ i, 0 < b.coord i y) :
    ∃ δ β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ x : ι → E,
      (∀ i, dist (x i) (b i) < δ) → AffineIndependent ℝ x ∧
        Metric.closedBall y β ⊆ convexHull ℝ (range x) := by
  obtain ⟨δ,hδ,h⟩ := simplex_reconstruction b hy
  refine ⟨δ,δ/2,hδ,by positivity,fun x hx => ?_⟩
  have hind := (h x y hx (by simpa using hδ)).1
  refine ⟨hind,fun z hz => ?_⟩
  have hz' : dist z y < δ := (Metric.mem_closedBall.mp hz).trans_lt (by linarith)
  obtain ⟨w,hw,hsum,hrec⟩ := (h x z hx hz').2
  rw [← hrec, ← Finset.univ.affineCombination_eq_linear_combination _ _ hsum]
  exact affineCombination_mem_convexHull (fun i _ => (hw i).le) hsum

private theorem common_flat_reconstruction
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (b : AffineBasis ι ℝ E) (hcard : Fintype.card ι = Module.finrank ℝ E + 1)
    {y : E} (hy : ∀ i, 0 < b.coord i y)
    (f : V →ᵃ[ℝ] E) (q : ι → V) (hq : ∀ i, f (q i) = b i)
    (r₀ : V) (hr₀ : f r₀ = y) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x : ι → V) (r : V) (W : AffineSubspace ℝ V),
      (∀ i, dist (x i) (q i) < ε) → dist r r₀ < ε →
      (∀ i, x i ∈ W) → r ∈ W → Module.finrank ℝ W.direction ≤ Module.finrank ℝ E →
      AffineIndependent ℝ x ∧ ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧
        ∑ i, w i = 1 ∧ ∑ i, w i • x i = r := by
  classical
  obtain ⟨δ,hδ,h⟩ := simplex_reconstruction b hy
  obtain ⟨K,hK⟩ := f.lipschitzWith_of_finiteDimensional
  let ε := δ / ((K:ℝ)+1)
  have hK1 : 0 < (K:ℝ)+1 := by positivity
  have hε : 0 < ε := div_pos hδ hK1
  have hnear {v w : V} (hv : dist v w < ε) : dist (f v) (f w) < δ := by
    calc
      _ ≤ (K:ℝ)*dist v w := hK.dist_le_mul _ _
      _ ≤ ((K:ℝ)+1)*dist v w := by nlinarith [dist_nonneg (x:=v) (y:=w)]
      _ < ((K:ℝ)+1)*ε := mul_lt_mul_of_pos_left hv hK1
      _ = δ := mul_div_cancel₀ _ hK1.ne'
  refine ⟨ε,hε,fun x r W hx hr hxW hrW hdim => ?_⟩
  have hx' : ∀ i, dist (f (x i)) (b i) < δ := fun i => hq i ▸ hnear (hx i)
  have hr' : dist (f r) y < δ := hr₀ ▸ hnear hr
  obtain ⟨hind,w,hw,hsum,hrec⟩ := h (fun i => f (x i)) (f r) hx' hr'
  have hxi : AffineIndependent ℝ x := AffineIndependent.of_comp f hind
  have hle : affineSpan ℝ (range x) ≤ W := affineSpan_le.mpr (by rintro _ ⟨i,rfl⟩; exact hxW i)
  have hdimX : Module.finrank ℝ (affineSpan ℝ (range x)).direction = Module.finrank ℝ E := by
    rw [direction_affineSpan]
    exact hxi.finrank_vectorSpan hcard
  have hdimW : Module.finrank ℝ W.direction = Module.finrank ℝ E :=
    le_antisymm hdim (hdimX ▸ Submodule.finrank_mono (AffineSubspace.direction_le hle))
  have heq := hxi.affineSpan_eq_of_le_of_card_eq_finrank_add_one hle (hdimW ▸ hcard)
  have hrspan : r ∈ affineSpan ℝ (range x) := heq.symm ▸ hrW
  obtain ⟨v,hv,hvr⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hrspan
  have hfv : Finset.univ.affineCombination ℝ (fun i => f (x i)) v = f r := by
    change Finset.univ.affineCombination ℝ (f ∘ x) v = f r
    rw [← Finset.univ.map_affineCombination x v hv f, ← hvr]
  have hfw : Finset.univ.affineCombination ℝ (fun i => f (x i)) w = f r := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hsum]
    exact hrec
  have hwv : w = v := (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ
    (fun i => f (x i))).mp hind w v hsum hv (hfw.trans hfv.symm)
  refine ⟨hxi,w,hw,hsum,?_⟩
  rw [hwv,← Finset.univ.affineCombination_eq_linear_combination _ _ hv,← hvr]


end SimplexStability

omit [FiniteDimensional ℝ V] in
private theorem chart_direction {p : V} (a : ExclusionChart C u p) :
    (affineSpan ℝ (exclusion C u p)).direction = LinearMap.range a.param.linear := by
  have hspan : affineSpan ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin a.dim)) 1) = ⊤ :=
    (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
      ⟨0,mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
  rw [← a.whole,← AffineSubspace.map_span,hspan,AffineSubspace.map_direction,
    AffineSubspace.direction_top,Submodule.map_top]
omit [FiniteDimensional ℝ V] in
private theorem chart_dimension {p : V} (a : ExclusionChart C u p) :
    Module.finrank ℝ (affineSpan ℝ (exclusion C u p)).direction = a.dim := by
  rw [chart_direction,LinearMap.finrank_range_of_inj (a.param.linear_injective_iff.mpr a.injective)]
  simp
private theorem chart_dimension_bound {p : V} (a : ExclusionChart C u p) :
    a.dim ≤ Module.finrank ℝ (LinearMap.ker u) := by
  rw [← chart_dimension a,chart_direction]
  apply Submodule.finrank_mono
  rintro _ ⟨z,rfl⟩
  exact chart_unit_linear a z
/-- Actual source contacts exist for every relative-interior point and every
whole injective source chart, including segment balls and the chart center.
Strictly positive barycentric coordinates express interior of their simplex. -/
theorem source_contact_simplex (p : pure C u) (a : ExclusionChart C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p)) :
    ∃ (ξ : EuclideanSpace ℝ (Fin a.dim))
      (b : AffineBasis (Fin (a.dim + 1)) ℝ (EuclideanSpace ℝ (Fin a.dim))),
      a.param ξ = y ∧ ‖ξ‖ < 1 ∧ (∀ i, ‖b i‖ = 1) ∧
      (∀ i, 0 < b.coord i ξ) ∧ AffineIndependent ℝ (fun i => a.param (b i)) ∧
      Module.finrank ℝ (affineSpan ℝ (exclusion C u p)).direction = a.dim ∧
      LinearMap.range a.param.linear ≤ LinearMap.ker u := by
  rw [MixedExclusionGeometry.chart_intrinsic p a] at hy
  obtain ⟨ξ, hξ, rfl⟩ := hy
  have hξ' : ‖ξ‖ < 1 := by simpa using hξ
  obtain ⟨b, hb, hpos⟩ := sphere_affine_basis a.dim_pos hξ'
  refine ⟨ξ, b, rfl, hξ', hb, hpos, b.ind.map' a.param a.injective,
    chart_dimension a,?_⟩
  rintro _ ⟨z,rfl⟩
  exact chart_unit_linear a z


private def sourceInverse {p : V} (a : ExclusionChart C u p) :
    V →ᵃ[ℝ] EuclideanSpace ℝ (Fin a.dim) :=
  a.param.linear.leftInverse.toAffineMap.comp
    ((AffineMap.id ℝ V) - AffineMap.const ℝ V (a.param 0))
omit [FiniteDimensional ℝ V] in
private theorem sourceInverse_apply {p : V} (a : ExclusionChart C u p)
    (z : EuclideanSpace ℝ (Fin a.dim)) : sourceInverse a (a.param z) = z := by
  change a.param.linear.leftInverse (a.param z - a.param 0) = z
  change a.param.linear.leftInverse (a.param z -ᵥ a.param 0) = z
  rw [← a.param.linear_apply_vsub, vsub_eq_sub,sub_zero]
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (a.param.linear_injective_iff.mpr a.injective)) z
omit [FiniteDimensional ℝ V] in
private theorem not_positive_simplex_extreme {ι : Type*} [Fintype ι] [Nontrivial ι]
    (x : ι → V) (hind : AffineIndependent ℝ x) (r : pure C u)
    (hx : ∀ i, x i ∈ base C u) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hsum : ∑ i,w i = 1) (hrec : ∑ i,w i • x i = (r:V)) : False := by
  classical
  have hrh : (r:V) ∈ convexHull ℝ (range x) := by
    rw [← hrec,← Finset.univ.affineCombination_eq_linear_combination _ _ hsum]
    exact affineCombination_mem_convexHull (fun i _ => (hw i).le) hsum
  have hhull : convexHull ℝ (range x) ⊆ base C u :=
    convexHull_min (by rintro _ ⟨i,rfl⟩; exact hx i) (base_convex C u)
  obtain ⟨i,hi⟩ := extremePoints_convexHull_subset
    (inter_extremePoints_subset_extremePoints_of_subset hhull ⟨hrh,r.property⟩)
  have hcomb : Finset.univ.affineCombination ℝ x w =
      Finset.univ.affineCombination ℝ x (Pi.single i 1) := by
    rw [Finset.univ.affineCombination_eq_linear_combination _ _ hsum,hrec,
      Finset.univ.affineCombination_piSingle ℝ x (Finset.mem_univ i),hi]
  have hwone : w = Pi.single i 1 :=
    (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ x).mp hind w
      (Pi.single i 1) hsum (by simp) hcomb
  obtain ⟨j,hji⟩ := exists_ne i
  have hh := hw j
  rw [hwone,Pi.single_eq_of_ne hji] at hh
  exact lt_irrefl _ hh

/-- The actual maximum of an original normal on the entire normalized base. -/
def baseMaximum (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (b : V →L[ℝ] ℝ) : ℝ :=
  sSup (b '' base C u)
private theorem maximum_at (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) (t : pure C u)
    (b : V →L[ℝ] ℝ) (hm : ∀ x ∈ base C u, b x ≤ b t) : baseMaximum C u b = b t := by
  apply le_antisymm
  · exact csSup_le ⟨b t,mem_image_of_mem b (pure_mem t)⟩ (by rintro _ ⟨x,hx,rfl⟩; exact hm x hx)
  · exact le_csSup ((base_compact hc hs).bddAbove_image b.continuous.continuousOn)
      (mem_image_of_mem b (pure_mem t))
private theorem uniform_dual_bound (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) :
    ∃ A : ℝ, 0 < A ∧ ∀ (t : pure C u) (b : V →L[ℝ] ℝ),
      b ≠ 0 → (∀ x ∈ C, 0 ≤ b x) → b t = 0 →
      0 < baseMaximum C u b ∧ ‖b‖ ≤ A * baseMaximum C u b := by
  obtain ⟨A,hA⟩ := (effects_compact hs hg).isBounded.exists_norm_le
  refine ⟨max A 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun t b hb hp ht => ?_⟩
  have hb' : b.toLinearMap ≠ 0 := by intro he; exact hb ((by ext z; exact LinearMap.congr_fun he z))
  obtain ⟨s,hsD,hbs,hmax⟩ := positive_annihilator_maximum hc hs hg t b.toLinearMap hb' hp ht
  change 0 < b s at hbs
  change ∀ x ∈ base C u, b x ≤ b s at hmax
  have hM := maximum_at hc hs s b hmax
  have hnorm : ‖(b s)⁻¹ • b‖ ≤ A := hA _ (cone_bound (base_compact hc hs) hs (fun r => by
    change 0 ≤ (b s)⁻¹ * b r ∧ (b s)⁻¹ * b r ≤ 1
    exact ⟨mul_nonneg (inv_nonneg.mpr hbs.le) (hp r (pure_mem r).1),
      (by rw [← div_eq_inv_mul,div_le_one hbs]; exact hmax r (pure_mem r))⟩))
  rw [norm_smul, Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hbs),← div_eq_inv_mul] at hnorm
  refine ⟨hM.symm ▸ hbs,?_⟩
  rw [hM]
  exact ((div_le_iff₀ hbs).mp hnorm).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hbs.le)

private theorem contact_estimate
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p t : pure C u) (a : ExclusionChart C u p) (b : V →L[ℝ] ℝ)
    (hb : b ≠ 0) (hp : ∀ x ∈ C, 0 ≤ b x) (ht : b t = 0)
    {A α : ℝ} (hA : ‖b‖ ≤ A * baseMaximum C u b)
    (hα : ∀ x ∈ exclusion C u t, Metric.infDist x (exclusion C u p) ≤ α)
    (hg0 : slope a b ≠ 0) (v : EuclideanSpace ℝ (Fin a.dim)) :
    ∃ x : pure C u, (x : V) ∈ exclusion C u t ∧
      ‖(x : V) - a.param v‖ ≤ α + ‖a.param.linear.toContinuousLinearMap‖ *
        (Real.sqrt (2*A*baseMaximum C u b*α/‖slope a b‖) +
          ‖‖slope a b‖⁻¹ • slope a b - v‖) := by
  have hb' : b.toLinearMap ≠ 0 := by intro he; exact hb ((by ext z; exact LinearMap.congr_fun he z))
  obtain ⟨x,hx,hbx,hmax⟩ := positive_annihilator_maximum hc hs hg t b.toLinearMap hb' hp ht
  change 0 < b x at hbx
  change ∀ z ∈ base C u, b z ≤ b x at hmax
  have hM : baseMaximum C u b = b x := maximum_at hc hs x b hmax
  obtain ⟨z,hz,hzdist⟩ := ((exclusion_ball_faces hc hs hg hB).1 p).2.1.exists_infDist_eq_dist
    ((exclusion_ball_faces hc hs hg hB).1 p).1.nonempty (x:V)
  have hxz : ‖(x:V)-z‖ ≤ α := by rw [← dist_eq_norm,← hzdist]; exact hα x hx
  obtain ⟨q,hq,rfl⟩ := a.whole.symm ▸ hz
  have hq1 : ‖q‖ ≤ 1 := by simpa using hq
  let s := ‖slope a b‖
  let w := s⁻¹ • slope a b
  have hspos : 0 < s := norm_pos_iff.mpr hg0
  have hw : ‖w‖ = 1 := by simp [w,s,norm_smul,hspos.ne']
  have hsw : s • w = slope a b := by simp [w,smul_smul,hspos.ne']
  have htop : b (a.param 0) + s ≤ b x := by
    have hh := hmax (a.param w) (chart_mem a hw.le).1
    rw [slope_formula,← hsw,real_inner_smul_left,real_inner_self_eq_norm_sq,hw] at hh
    simpa using hh
  have hgap : s * (1-⟪w,q⟫) ≤ A*baseMaximum C u b*α := by
    have hh := b.le_opNorm ((x:V)-a.param q)
    have hn : b ((x:V)-a.param q) ≤ ‖b ((x:V)-a.param q)‖ := le_abs_self _
    have hbq := slope_formula a b q
    rw [← hsw,real_inner_smul_left] at hbq
    rw [map_sub] at hn hh
    have hα0 : 0 ≤ α := (norm_nonneg _).trans hxz
    have hh2 := mul_le_mul hA hxz (norm_nonneg _) (le_trans (norm_nonneg _) hA)
    nlinarith
  have hnormsq : ‖q-w‖^2 ≤ 2*(1-⟪w,q⟫) := by
    rw [norm_sub_sq_real,hw,real_inner_comm]
    nlinarith [sq_nonneg ‖q‖,mul_self_le_mul_self (norm_nonneg q) hq1]
  have hsq : ‖q-w‖^2 ≤ 2*A*baseMaximum C u b*α/s := by
    apply (le_div_iff₀ hspos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hnormsq hspos.le]
  have hsqrt : ‖q-w‖ ≤ Real.sqrt (2*A*baseMaximum C u b*α/s) :=
    (Real.le_sqrt (norm_nonneg _) (le_trans (sq_nonneg _) hsq)).mpr hsq
  refine ⟨x,hx,?_⟩
  have hpardiff : a.param q - a.param v = a.param.linear (q-v) := by
    simpa using (a.param.linear_apply_vsub q v).symm
  calc
    _ ≤ ‖(x:V)-a.param q‖ + ‖a.param q-a.param v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ α + ‖a.param.linear.toContinuousLinearMap‖ * ‖q-v‖ := by
      rw [hpardiff]; exact add_le_add hxz (a.param.linear.toContinuousLinearMap.le_opNorm _)
    _ ≤ _ := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_sub_le_norm_sub_add_norm_sub q w v).trans (add_le_add_left hsqrt _)

private theorem leakage_point_le (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p t : pure C u) {x : V} (hx : x ∈ exclusion C u t) :
    Metric.infDist x (exclusion C u p) ≤ leakage C u p t := by
  exact le_csSup (((exclusion_ball_faces hc hs hg hB).1 t).2.1.bddAbove_image
    (Metric.continuous_infDist_pt _).continuousOn) (mem_image_of_mem _ hx)

/-- All source directions fail at the same actual return label. This is an
extra condition on original positive normals, with no effect-budget bound. -/
def sectorViolation {p : V} (a : ExclusionChart C u p)
    (v : Fin (a.dim+1) → EuclideanSpace ℝ (Fin a.dim)) (t : V) (θ H : ℝ) : Prop :=
  ∀ i, ∃ f : V →L[ℝ] ℝ, f ≠ 0 ∧ (∀ x ∈ C, 0 ≤ f x) ∧ f t = 0 ∧
    slope a f ≠ 0 ∧ ‖‖slope a f‖⁻¹ • slope a f - v i‖ < θ ∧
    H * baseMaximum C u f * leakage C u p t < ‖slope a f‖

private theorem sector_contact_family (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (a : ExclusionChart C u p)
    (b : Fin (a.dim+1) → EuclideanSpace ℝ (Fin a.dim)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ H : ℝ, 0 < θ ∧ 0 < H ∧ ∀ t : pure C u,
      leakage C u p t < δ/4 → sectorViolation a b t θ H →
      ∃ x : Fin (a.dim+1) → pure C u, ∀ i,
        (x i:V) ∈ exclusion C u t ∧ dist (x i:V) (a.param (b i)) < δ := by
  classical
  obtain ⟨A,hA,hdual⟩ := uniform_dual_bound hc hs hg
  let T := ‖a.param.linear.toContinuousLinearMap‖
  let θ := δ / (4*(T+1))
  let H := 2*A/θ^2
  have hT : 0 ≤ T := norm_nonneg _
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨θ,H,hθ,hH,fun t hα hn => ?_⟩
  choose f hf0 hfpos hft hfg hfdir hfbig using hn
  have hcontacts (i : Fin (a.dim+1)) : ∃ x : pure C u,
      (x:V) ∈ exclusion C u t ∧ dist (x:V) (a.param (b i)) < δ := by
    obtain ⟨hM,hbound⟩ := hdual t (f i) (hf0 i) (hfpos i) (hft i)
    obtain ⟨x,hx,he⟩ := contact_estimate hc hs hg hB p t a (f i) (hf0 i)
      (hfpos i) (hft i) hbound (fun x hx => leakage_point_le hc hs hg hB p t hx)
      (hfg i) (b i)
    have hspos : 0 < ‖slope a (f i)‖ := norm_pos_iff.mpr (hfg i)
    have hratio : 2*A*baseMaximum C u (f i)*leakage C u p t/‖slope a (f i)‖ ≤ θ^2 := by
      apply (div_le_iff₀ hspos).mpr
      have hh := mul_le_mul_of_nonneg_right (hfbig i).le (sq_nonneg θ)
      have hHθ : H*θ^2 = 2*A := div_mul_cancel₀ _ (pow_ne_zero 2 hθ.ne')
      calc
        _ = (H*θ^2)*baseMaximum C u (f i)*leakage C u p t := by rw [hHθ]
        _ = H*baseMaximum C u (f i)*leakage C u p t*θ^2 := by ring
        _ ≤ _ := by simpa only [mul_comm] using hh
    have hsqrt : Real.sqrt (2*A*baseMaximum C u (f i)*leakage C u p t/‖slope a (f i)‖) ≤ θ :=
      (Real.sqrt_le_iff).mpr ⟨hθ.le,hratio⟩
    have hsmall : T*(θ+θ) < δ/2 := by
      have heq : (4*(T+1))*θ = δ := mul_div_cancel₀ _ (by positivity)
      nlinarith
    refine ⟨x,hx,?_⟩
    rw [dist_eq_norm]
    calc
      _ ≤ _ := he
      _ ≤ leakage C u p t + T*(θ+θ) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left
          (add_le_add hsqrt (hfdir i).le) hT) _
      _ < δ := by linarith
  choose x hx hxdist using hcontacts
  exact ⟨x,fun i => ⟨hx i,hxdist i⟩⟩

/-- A single sector is valid for every original positive annihilator after
all constants have been chosen, without a bound on its global maximum. -/
theorem uniform_return_sectors (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) (a : ExclusionChart C u p)
    {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (ξ : EuclideanSpace ℝ (Fin a.dim)) (hξ : a.param ξ = y)
    (b : AffineBasis (Fin (a.dim+1)) ℝ (EuclideanSpace ℝ (Fin a.dim)))
    (_hb : ∀ i, ‖b i‖ = 1) (hpos : ∀ i, 0 < b.coord i ξ) :
    ∃ ε θ H : ℝ, 0 < ε ∧ 0 < θ ∧ 0 < H ∧
      ∀ r t : pure C u, dist (r:V) y < ε → (t:V) ∈ exclusion C u r →
        Module.finrank ℝ (affineSpan ℝ (exclusion C u t)).direction ≤ a.dim →
        ∃ i : Fin (a.dim+1), ∀ f : V →L[ℝ] ℝ,
          f ≠ 0 → (∀ x ∈ C, 0 ≤ f x) → f t = 0 → slope a f ≠ 0 →
          ‖‖slope a f‖⁻¹ • slope a f - b i‖ < θ →
          ‖slope a f‖ ≤ H * baseMaximum C u f * leakage C u p t := by
  classical
  obtain ⟨δ,hδ,hstable⟩ := common_flat_reconstruction b (by simp) hpos
    (sourceInverse a) (fun i => a.param (b i)) (fun i => sourceInverse_apply a _)
    y (by rw [← hξ,sourceInverse_apply])
  obtain ⟨θ,H,hθ,hH,hcontact⟩ := sector_contact_family hc hs hg hB p a b hδ
  obtain ⟨ε₀,hε₀,hleak⟩ := whole_return_leakage hc hs hg hB p hy
    (show 0 < δ/4 by positivity)
  refine ⟨min ε₀ δ,θ,H,lt_min hε₀ hδ,hθ,hH,fun r t hr ht hdim => ?_⟩
  by_contra! hn
  have hα : leakage C u p t < δ/4 := hleak r t (hr.trans_le (min_le_left _ _)) ht
  obtain ⟨x,hx⟩ := hcontact t hα hn
  have hrD : (r:V) ∈ exclusion C u t := (exclusion_symmetric r t).mp ht
  obtain ⟨hind,w,hw,hsum,hrec⟩ := hstable (fun i => (x i:V)) r
    (affineSpan ℝ (exclusion C u t)) (fun i => (hx i).2) (hr.trans_le (min_le_right _ _))
    (fun i => subset_affineSpan ℝ _ (hx i).1) (subset_affineSpan ℝ _ hrD)
    (by simpa using hdim)
  have : Nontrivial (Fin (a.dim+1)) :=
    Fin.nontrivial_iff_two_le.mpr (Nat.succ_le_succ a.dim_pos)
  exact not_positive_simplex_extreme (fun i => (x i:V)) hind r
    (fun i => pure_mem (x i)) w hw hsum hrec


private theorem chart_operator_bound
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    {p : V} (a : ExclusionChart C u p) :
    ‖a.param.linear.toContinuousLinearMap‖ ≤ Metric.diam (base C u)/2 := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro z hz
  have hd := Metric.dist_le_diam_of_mem (base_compact hc hs).isBounded
    (chart_mem a hz.le).1 (chart_mem a (by simpa using hz.le : ‖-z‖ ≤ 1)).1
  have he : a.param z - a.param (-z) = (2:ℝ) • a.param.linear z := by
    rw [← vsub_eq_sub,← a.param.linear_apply_vsub,vsub_eq_sub]
    have hh : z - -z = (2:ℝ) • z := by module
    rw [hh,map_smul]
  rw [dist_eq_norm,he,norm_smul] at hd
  norm_num at hd
  change ‖a.param.linear z‖ ≤ _
  linarith

private theorem base_radius_positive
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (p : pure C u) (a : ExclusionChart C u p) : 0 < Metric.diam (base C u)/2 := by
  let z : EuclideanSpace ℝ (Fin a.dim) := EuclideanSpace.single ⟨0,a.dim_pos⟩ 1
  have hz : ‖z‖ = 1 := by simp [z]
  have hzne : z ≠ -z := by
    intro he
    have hh := congrArg (fun v : EuclideanSpace ℝ (Fin a.dim) => v ⟨0,a.dim_pos⟩) he
    norm_num [z] at hh
  have hne : a.param z ≠ a.param (-z) := a.injective.ne hzne
  have hh := Metric.dist_le_diam_of_mem (base_compact hc hs).isBounded
    (chart_mem a hz.le).1 (chart_mem a (by simpa using hz.le : ‖-z‖ ≤ 1)).1
  have hpos := (dist_pos.mpr hne).trans_le hh
  positivity

private theorem actual_parameter_unit
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (r t : pure C u) (ht : (t:V) ∈ exclusion C u r)
    (a : ExclusionChart C u t) (z : EuclideanSpace ℝ (Fin a.dim))
    (hz : a.param z = r) : ‖z‖ = 1 := by
  have hr : (r:V) ∈ exclusion C u t ∩ pure C u :=
    ⟨(exclusion_symmetric r t).mp ht,r.property⟩
  rw [chart_boundary hc hs hg hB t a] at hr
  obtain ⟨w,hw,he⟩ := hr
  have hzw := a.injective (hz.trans he.symm)
  rw [hzw]
  simpa using hw

private theorem actual_leakage_tendsto
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) {y : V} (hy : y ∈ intrinsicInterior ℝ (exclusion C u p))
    (r t : ℕ → pure C u) (hr : Tendsto (fun n => (r n:V)) atTop (𝓝 y))
    (ht : ∀ n, (t n:V) ∈ exclusion C u (r n)) :
    Tendsto (fun n => leakage C u p (t n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨ε,hε,h⟩ := whole_return_leakage hc hs hg hB p hy hδ
  filter_upwards [Metric.tendsto_nhds.mp hr ε hε] with n hn
  have hα0 : 0 ≤ leakage C u p (t n) := by
    obtain ⟨x,hx⟩ := ((exclusion_ball_faces hc hs hg hB).1 (t n)).1.nonempty
    exact Metric.infDist_nonneg.trans (leakage_point_le hc hs hg hB p (t n) hx)
  simpa [Real.dist_eq,abs_of_nonneg hα0] using h (r n) (t n) hn (ht n)

section MinimumNorm
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] in
private theorem ker_orthogonal_injective (A : E →L[ℝ] F) {x y : E}
    (hx : x ∈ A.kerᗮ) (hy : y ∈ A.kerᗮ) (he : A x = A y) : x = y := by
  apply sub_eq_zero.mp
  have hk : x-y ∈ A.ker := by simpa [LinearMap.mem_ker, map_sub] using sub_eq_zero.mpr he
  have ho : x-y ∈ A.kerᗮ := A.kerᗮ.sub_mem hx hy
  have hh := (Submodule.mem_orthogonal _ _).mp ho (x-y) hk
  exact inner_self_eq_zero.mp hh

private theorem map_orthogonal_projection (A : E →L[ℝ] F) (x : E) :
    A (A.kerᗮ.starProjection x) = A x := by
  have hd := A.ker.starProjection_add_starProjection_orthogonal x
  have hp : A (A.ker.starProjection x) = 0 :=
    (A.ker.orthogonalProjectionOnto x).property
  have hh := congrArg A hd
  simpa only [map_add, hp, zero_add] using hh

private theorem kernel_margin (A : E →L[ℝ] F) {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρR : ρ ≤ R) (hA : ‖A‖ ≤ R)
    {z : E} (hz : ‖z‖ = 1)
    (hball : Metric.closedBall (A z) ρ ⊆ A '' Metric.closedBall 0 1) :
    ‖A.kerᗮ.starProjection z‖ ≤ 1 - ρ / R ∧
      1 - (1 - ρ/R)^2 ≤ ‖A.ker.starProjection z‖^2 := by
  let w := A.kerᗮ.starProjection z
  have hwmem : w ∈ A.kerᗮ := (A.kerᗮ.orthogonalProjectionOnto z).property
  have hwmap : A w = A z := map_orthogonal_projection A z
  have hwle : ‖w‖ ≤ 1 := by simpa only [hz] using A.kerᗮ.norm_starProjection_apply_le z
  have hbnd : ‖w‖ ≤ 1 - ρ/R := by
    by_cases hw : w = 0
    · simpa only [hw,norm_zero] using sub_nonneg.mpr ((div_le_one hR).mpr hρR)
    have hwpos := norm_pos_iff.mpr hw
    have hAw : A w ≠ 0 := by
      intro hh
      exact hw (ker_orthogonal_injective A hwmem (Submodule.zero_mem _) (by simpa using hh))
    have hAwpos := norm_pos_iff.mpr hAw
    let s := 1 + ρ / ‖A w‖
    have hs : 0 < s := by dsimp [s]; positivity
    have hsmem : s • A w ∈ Metric.closedBall (A z) ρ := by
      have heq : s • A w - A w = (s-1) • A w := by module
      rw [Metric.mem_closedBall, ← hwmap, dist_eq_norm, heq]
      simp only [s,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
        abs_of_pos (div_pos hρ hAwpos),div_mul_cancel₀ _ hAwpos.ne']
      exact le_rfl
    obtain ⟨v,hv,he⟩ := hball hsmem
    have hproj : A.kerᗮ.starProjection v = s • w := by
      apply ker_orthogonal_injective A (A.kerᗮ.orthogonalProjectionOnto v).property
        (A.kerᗮ.smul_mem s hwmem)
      change A (A.kerᗮ.starProjection v) = A (s • w)
      rw [map_orthogonal_projection, map_smul, he]
    have hvnorm : ‖v‖ ≤ 1 := by simpa using hv
    have hh := (A.kerᗮ.norm_starProjection_apply_le v).trans hvnorm
    rw [hproj, norm_smul, Real.norm_eq_abs, abs_of_pos hs] at hh
    have hAnorm : ‖A w‖ ≤ R * ‖w‖ :=
      (A.le_opNorm w).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg w))
    have hmul : ρ * ‖w‖ ≤ (1-‖w‖) * ‖A w‖ := by
      have hhd : ρ / ‖A w‖ * ‖w‖ ≤ 1-‖w‖ := by
        dsimp [s] at hh
        nlinarith
      rw [div_mul_eq_mul_div] at hhd
      exact (div_le_iff₀ hAwpos).mp hhd
    have hsecond := mul_le_mul_of_nonneg_left hAnorm (sub_nonneg.mpr hwle)
    have hρle : ρ ≤ (1-‖w‖)*R := by nlinarith
    have hhdiv := (div_le_iff₀ hR).mpr hρle
    linarith
  refine ⟨hbnd, ?_⟩
  have hp := A.ker.norm_sq_eq_add_norm_sq_starProjection z
  rw [hz] at hp
  have hnon : 0 ≤ 1-ρ/R := sub_nonneg.mpr ((div_le_one hR).mpr hρR)
  have hsquare := pow_le_pow_left₀ (norm_nonneg w) hbnd 2
  dsimp [w] at hsquare
  nlinarith


private theorem projection_mass_transfer (J T : Submodule ℝ E) {ε : ℝ}
    (hε : 0 ≤ ε) (hangle : ∀ v ∈ J, ‖T.starProjection v‖ ≤ ε * ‖v‖)
    {z : E} (hz : ‖z‖ = 1) :
    ‖J.starProjection z‖ ≤ ‖Tᗮ.starProjection z‖ + ε := by
  let v := J.starProjection z
  have hvJ : v ∈ J := (J.orthogonalProjectionOnto z).property
  have hvz : ⟪v,z⟫ = ‖v‖^2 := by
    have hh := J.starProjection_inner_eq_zero z v hvJ
    rw [inner_sub_left] at hh
    rw [real_inner_comm]
    change ⟪z,v⟫ - ⟪v,v⟫ = 0 at hh
    simpa only [real_inner_self_eq_norm_sq] using (sub_eq_zero.mp hh)
  have hT := T.starProjection_add_starProjection_orthogonal z
  have hvT : ⟪v,T.starProjection z⟫ = ⟪T.starProjection v,T.starProjection z⟫ := by
    have hh := T.starProjection_inner_eq_zero v (T.starProjection z)
      (T.orthogonalProjectionOnto z).property
    simpa only [inner_sub_left,sub_eq_zero] using hh
  have hc1 := real_inner_le_norm (T.starProjection v) (T.starProjection z)
  have hc2 := real_inner_le_norm v (Tᗮ.starProjection z)
  have hTnorm : ‖T.starProjection z‖ ≤ 1 := by simpa only [hz] using T.norm_starProjection_apply_le z
  have hangle' := hangle v hvJ
  have hprod : ‖T.starProjection v‖ * ‖T.starProjection z‖ ≤ ε * ‖v‖ := by
    calc
      _ ≤ ‖T.starProjection v‖ * 1 := mul_le_mul_of_nonneg_left hTnorm (norm_nonneg _)
      _ ≤ _ := by simpa using hangle'
  have hsum : ‖v‖^2 ≤ ε*‖v‖ + ‖v‖*‖Tᗮ.starProjection z‖ := by
    calc
      ‖v‖^2 = ⟪v,z⟫ := hvz.symm
      _ = ⟪T.starProjection v,T.starProjection z⟫ + ⟪v,Tᗮ.starProjection z⟫ := by
        conv_lhs => rw [← hT, inner_add_right, hvT]
      _ ≤ _ := add_le_add (hc1.trans hprod) hc2
  by_cases hv : v = 0
  · change ‖v‖ ≤ _
    rw [hv,norm_zero]
    exact add_nonneg (norm_nonneg _) hε
  have hvpos := norm_pos_iff.mpr hv
  dsimp [v] at hsum hvpos ⊢
  nlinarith


end MinimumNorm

section EuclideanReturns
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {C₁ : PointedCone ℝ E} {u₁ : E →ₗ[ℝ] ℝ}

/-- Orthogonal affine projection onto the direction of the whole source face. -/
def sourceProjection (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) : E →ᵃ[ℝ] E :=
  let U := (affineSpan ℝ (exclusion C₁ u₁ p)).direction
  U.starProjection.toLinearMap.toAffineMap.comp
    ((AffineMap.id ℝ E) - AffineMap.const ℝ E (a.param 0)) +
      AffineMap.const ℝ E (a.param 0)

private theorem sourceProjection_linear (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) :
    (sourceProjection p a).linear =
      (affineSpan ℝ (exclusion C₁ u₁ p)).direction.starProjection.toLinearMap := by
  simp [sourceProjection]

private theorem sourceProjection_fix (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {z : E} (hz : z ∈ affineSpan ℝ (exclusion C₁ u₁ p)) : sourceProjection p a z = z := by
  have hc : a.param 0 ∈ affineSpan ℝ (exclusion C₁ u₁ p) :=
    subset_affineSpan ℝ _ (chart_mem a (by simp : ‖(0 : EuclideanSpace ℝ (Fin a.dim))‖ ≤ 1))
  have hd := (affineSpan ℝ (exclusion C₁ u₁ p)).vsub_mem_direction hz hc
  change z-a.param 0 ∈ (affineSpan ℝ (exclusion C₁ u₁ p)).direction at hd
  change (affineSpan ℝ (exclusion C₁ u₁ p)).direction.starProjection (z-a.param 0) + a.param 0 = z
  rw [Submodule.starProjection_eq_self_iff.mpr hd,sub_add_cancel]

private theorem sourceProjection_dist (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {z : E} (hz : z ∈ affineSpan ℝ (exclusion C₁ u₁ p)) (x : E) :
    dist (sourceProjection p a x) z ≤ dist x z := by
  calc
    _ = dist (sourceProjection p a x) (sourceProjection p a z) := by rw [sourceProjection_fix p a hz]
    _ = ‖(affineSpan ℝ (exclusion C₁ u₁ p)).direction.starProjection (x-z)‖ := by
      rw [dist_eq_norm,← vsub_eq_sub,← (sourceProjection p a).linear_apply_vsub,sourceProjection_linear]
      rfl
    _ ≤ dist x z := by simpa [dist_eq_norm] using (affineSpan ℝ (exclusion C₁ u₁ p)).direction.norm_starProjection_apply_le (x-z)

omit [FiniteDimensional ℝ E] in
private theorem chart_inverse_reconstruct (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {z : E} (hz : z ∈ affineSpan ℝ (exclusion C₁ u₁ p)) : a.param (sourceInverse a z) = z := by
  have hspan : affineSpan ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin a.dim)) 1) = ⊤ :=
    (convex_closedBall _ _).interior_nonempty_iff_affineSpan_eq_top.mp
      ⟨0,mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ zero_lt_one)⟩
  rw [← a.whole,← AffineSubspace.map_span,hspan] at hz
  obtain ⟨q,_,rfl⟩ := hz
  rw [sourceInverse_apply]

private theorem sourceProjection_mem (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) (z : E) :
    sourceProjection p a z ∈ affineSpan ℝ (exclusion C₁ u₁ p) := by
  have hc := subset_affineSpan ℝ (exclusion C₁ u₁ p) (chart_mem a (by simp : ‖(0 : EuclideanSpace ℝ (Fin a.dim))‖ ≤ 1))
  apply (affineSpan ℝ (exclusion C₁ u₁ p)).vadd_mem_of_mem_direction
    (v := (affineSpan ℝ (exclusion C₁ u₁ p)).direction.starProjection (z-a.param 0))
    (Submodule.starProjection_apply_mem _ _) hc

private theorem projected_simplex_ball (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {y : E} (ξ : EuclideanSpace ℝ (Fin a.dim)) (hξ : a.param ξ = y)
    (b : AffineBasis (Fin (a.dim+1)) ℝ (EuclideanSpace ℝ (Fin a.dim)))
    (hunit : ∀ i, ‖b i‖ = 1) (hpos : ∀ i, 0 < b.coord i ξ) :
    ∃ δ β : ℝ, 0 < δ ∧ 0 < β ∧ ∀ x : Fin (a.dim+1) → E,
      (∀ i, dist (x i) (a.param (b i)) < δ) →
      Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
        convexHull ℝ (range (fun i => sourceProjection p a (x i))) := by
  obtain ⟨δ₀,β₀,hδ₀,hβ₀,hball⟩ := fixed_simplex_ball b hpos
  obtain ⟨K,hK⟩ := (sourceInverse a).lipschitzWith_of_finiteDimensional
  let D := (K:ℝ)+1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨δ₀/D,β₀/D,div_pos hδ₀ hD,div_pos hβ₀ hD,fun x hx z hz => ?_⟩
  have hproj (i) : dist (sourceInverse a (sourceProjection p a (x i))) (b i) < δ₀ := by
    rw [← sourceInverse_apply a (b i)]
    calc
      _ ≤ (K:ℝ)*dist (sourceProjection p a (x i)) (a.param (b i)) := hK.dist_le_mul _ _
      _ ≤ (K:ℝ)*dist (x i) (a.param (b i)) := mul_le_mul_of_nonneg_left
        (sourceProjection_dist p a (subset_affineSpan ℝ _ (chart_mem a (hunit i).le)) _) K.coe_nonneg
      _ ≤ D*dist (x i) (a.param (b i)) := by dsimp [D]; nlinarith [dist_nonneg (x:=x i) (y:=a.param (b i))]
      _ < D*(δ₀/D) := mul_lt_mul_of_pos_left (hx i) hD
      _ = δ₀ := mul_div_cancel₀ _ hD.ne'
  have hz' : sourceInverse a z ∈ Metric.closedBall ξ β₀ := by
    rw [Metric.mem_closedBall,← sourceInverse_apply a ξ,hξ]
    calc
      _ ≤ (K:ℝ)*dist z y := hK.dist_le_mul _ _
      _ ≤ D*dist z y := by dsimp [D]; nlinarith [dist_nonneg (x:=z) (y:=y)]
      _ ≤ D*(β₀/D) := mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hz.1) hD.le
      _ = β₀ := mul_div_cancel₀ _ hD.ne'
  have hzm := (hball (fun i => sourceInverse a (sourceProjection p a (x i))) hproj).2 hz'
  have him := mem_image_of_mem a.param hzm
  rw [a.param.image_convexHull] at him
  have hrange : a.param '' range (fun i => sourceInverse a (sourceProjection p a (x i))) =
      range (fun i => sourceProjection p a (x i)) := by
    rw [← range_comp]
    congr 1
    ext i
    exact chart_inverse_reconstruct p a (sourceProjection_mem p a (x i))
  rw [hrange,chart_inverse_reconstruct p a hz.2] at him
  exact him

/-- The actual return linear chart followed by the orthogonal source projection,
with its codomain restricted to the source direction. -/
def projectedLinear (p : pure C₁ u₁) {t : E}
    (c : ExclusionChart C₁ u₁ t) :
    EuclideanSpace ℝ (Fin c.dim) →L[ℝ] (affineSpan ℝ (exclusion C₁ u₁ p)).direction :=
  (affineSpan ℝ (exclusion C₁ u₁ p)).direction.orthogonalProjectionOnto.comp
    c.param.linear.toContinuousLinearMap

private theorem projectedLinear_formula (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {t : E} (c : ExclusionChart C₁ u₁ t) (z : EuclideanSpace ℝ (Fin c.dim)) :
    sourceProjection p a (c.param z) =
      (projectedLinear p c z:E) + sourceProjection p a (c.param 0) := by
  have h := (sourceProjection p a).linear_apply_vsub (c.param z) (c.param 0)
  rw [sourceProjection_linear] at h
  have hc : c.param z -ᵥ c.param 0 = c.param.linear z := by
    rw [← c.param.linear_apply_vsub,vsub_eq_sub,sub_zero]
  rw [hc] at h
  change (projectedLinear p c z:E) = sourceProjection p a (c.param z) - sourceProjection p a (c.param 0) at h
  exact (eq_sub_iff_add_eq.mp h).symm

private theorem actual_projected_margin
    (hc : IsClosed (C₁ : Set E)) (hs : ∀ x ∈ C₁, x ≠ 0 → 0 < u₁ x)
    (hg : Submodule.span ℝ (C₁ : Set E) = ⊤) (hB : exclusionBalls C₁ u₁)
    (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {y : E} (hy : y ∈ affineSpan ℝ (exclusion C₁ u₁ p))
    {β : ℝ} (_hβ : 0 < β) (hβR : β < Metric.diam (base C₁ u₁)/2)
    (r t : pure C₁ u₁) (ht : (t:E) ∈ exclusion C₁ u₁ r)
    (c : ExclusionChart C₁ u₁ t) (z : EuclideanSpace ℝ (Fin c.dim)) (hz : c.param z = r)
    (hnear : dist (r:E) y < β)
    (hball : Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
      sourceProjection p a '' exclusion C₁ u₁ t) :
    1-(1-(β-dist (r:E) y)/(Metric.diam (base C₁ u₁)/2))^2 ≤
      ‖(projectedLinear p c).ker.starProjection z‖^2 := by
  let U := (affineSpan ℝ (exclusion C₁ u₁ p)).direction
  let A := projectedLinear p c
  let R := Metric.diam (base C₁ u₁)/2
  let ρ := β-dist (r:E) y
  have hR : 0 < R := base_radius_positive hc hs p a
  have hρ : 0 < ρ := sub_pos.mpr hnear
  have hρR : ρ ≤ R := by dsimp [ρ,R]; linarith [dist_nonneg (x:=(r:E)) (y:=y)]
  have hA : ‖A‖ ≤ R := by
    apply A.opNorm_le_bound hR.le
    intro v
    change ‖U.starProjection (c.param.linear v)‖ ≤ _
    exact (U.norm_starProjection_apply_le (c.param.linear v)).trans
      ((c.param.linear.toContinuousLinearMap.le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (chart_operator_bound hc hs c) (norm_nonneg v)))
  have heval : sourceProjection p a (r:E) = (A z:E) + sourceProjection p a (c.param 0) := by
    rw [← hz]; exact projectedLinear_formula p a c z
  have hballA : Metric.closedBall (A z) ρ ⊆ A '' Metric.closedBall 0 1 := by
    intro v hv
    let q : E := (v:E) + sourceProjection p a (c.param 0)
    have hqF : q ∈ affineSpan ℝ (exclusion C₁ u₁ p) :=
      (affineSpan ℝ (exclusion C₁ u₁ p)).vadd_mem_of_mem_direction
        v.property (sourceProjection_mem p a (c.param 0))
    have hqdist : dist q y ≤ β := by
      have hqr : dist q (sourceProjection p a (r:E)) ≤ ρ := by
        rw [heval]
        simpa only [q,dist_add_right,Subtype.dist_eq] using (Metric.mem_closedBall.mp hv)
      have hh := dist_triangle q (sourceProjection p a (r:E)) y
      have hp := sourceProjection_dist p a hy (r:E)
      dsimp [ρ] at hqr
      linarith
    obtain ⟨w,hw,he⟩ := hball ⟨Metric.mem_closedBall.mpr hqdist,hqF⟩
    obtain ⟨v₀,hv₀,rfl⟩ := c.whole.symm ▸ hw
    refine ⟨v₀,hv₀,?_⟩
    apply Subtype.val_injective
    have hh := projectedLinear_formula p a c v₀
    rw [he] at hh
    exact add_right_cancel hh.symm
  exact (kernel_margin A hR hρ hρR hA
    (actual_parameter_unit hc hs hg hB r t ht c z hz) hballA).2

private theorem normal_leakage
    (hc : IsClosed (C₁ : Set E)) (hs : ∀ x ∈ C₁, x ≠ 0 → 0 < u₁ x)
    (hg : Submodule.span ℝ (C₁ : Set E) = ⊤) (hB : exclusionBalls C₁ u₁)
    (p t : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) {x : E}
    (hx : x ∈ exclusion C₁ u₁ t) :
    ‖(affineSpan ℝ (exclusion C₁ u₁ p)).directionᗮ.starProjection (x-a.param 0)‖ ≤
      leakage C₁ u₁ p t := by
  let U := (affineSpan ℝ (exclusion C₁ u₁ p)).direction
  let Q := Uᗮ.starProjection
  obtain ⟨q,hq,hqdist⟩ := ((exclusion_ball_faces hc hs hg hB).1 p).2.1.exists_infDist_eq_dist
    ((exclusion_ball_faces hc hs hg hB).1 p).1.nonempty x
  have hcF := subset_affineSpan ℝ (exclusion C₁ u₁ p)
    (chart_mem a (by simp : ‖(0 : EuclideanSpace ℝ (Fin a.dim))‖ ≤ 1))
  have hqU := (affineSpan ℝ (exclusion C₁ u₁ p)).vsub_mem_direction (subset_affineSpan ℝ _ hq) hcF
  change q-a.param 0 ∈ U at hqU
  have hq0 : Q (q-a.param 0) = 0 := U.starProjection_orthogonal_apply_eq_zero hqU
  have he : Q (x-a.param 0) = Q (x-q)+Q (q-a.param 0) := by rw [← map_add]; congr 1; abel
  change ‖Q (x-a.param 0)‖ ≤ _
  rw [he,hq0,add_zero]
  exact (Uᗮ.norm_starProjection_apply_le (x-q)).trans
    (by rw [← dist_eq_norm,← hqdist]; exact leakage_point_le hc hs hg hB p t hx)

private theorem normal_operator_bound
    (hc : IsClosed (C₁ : Set E)) (hs : ∀ x ∈ C₁, x ≠ 0 → 0 < u₁ x)
    (hg : Submodule.span ℝ (C₁ : Set E) = ⊤) (hB : exclusionBalls C₁ u₁)
    (p t : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) (c : ExclusionChart C₁ u₁ t) :
    ‖(affineSpan ℝ (exclusion C₁ u₁ p)).directionᗮ.starProjection.comp
      c.param.linear.toContinuousLinearMap‖ ≤ leakage C₁ u₁ p t := by
  let U := (affineSpan ℝ (exclusion C₁ u₁ p)).direction
  let Q := Uᗮ.starProjection
  have hα : 0 ≤ leakage C₁ u₁ p t := by
    obtain ⟨x,hx⟩ := ((exclusion_ball_faces hc hs hg hB).1 t).1.nonempty
    exact Metric.infDist_nonneg.trans (leakage_point_le hc hs hg hB p t hx)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hα
  intro v hv
  have hp := normal_leakage hc hs hg hB p t a (chart_mem c hv.le)
  have hm := normal_leakage hc hs hg hB p t a (chart_mem c (by simpa using hv.le : ‖-v‖ ≤ 1))
  have hd : Q (c.param v-a.param 0)-Q (c.param (-v)-a.param 0) =
      (2:ℝ) • Q (c.param.linear v) := by
    rw [← map_sub]
    have he : c.param v-a.param 0-(c.param (-v)-a.param 0) = c.param v-c.param (-v) := by abel
    rw [he,← vsub_eq_sub,← c.param.linear_apply_vsub,vsub_eq_sub]
    have he : v- -v = (2:ℝ) • v := by module
    rw [he,map_smul,map_smul]
  have hh := norm_sub_le (Q (c.param v-a.param 0)) (Q (c.param (-v)-a.param 0))
  rw [hd,norm_smul] at hh
  norm_num at hh
  simp only [map_sub] at hp hm
  change ‖Q (c.param.linear v)‖ ≤ _
  linarith

private theorem projected_ball_dual_bound
    (p t : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) (c : ExclusionChart C₁ u₁ t)
    {y : E} (hy : y ∈ affineSpan ℝ (exclusion C₁ u₁ p)) {β : ℝ} (hβ : 0 < β)
    (hball : Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
      sourceProjection p a '' exclusion C₁ u₁ t) :
    ∀ h ∈ (affineSpan ℝ (exclusion C₁ u₁ p)).direction,
      β*‖h‖ ≤ ‖c.param.linear.toContinuousLinearMap.adjoint h‖ := by
  intro h hh
  by_cases hz : h = 0
  · simp [hz]
  let U := (affineSpan ℝ (exclusion C₁ u₁ p)).direction
  let e := ‖h‖⁻¹ • h
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hz
  have he : ‖e‖ = 1 := by simp [e,norm_smul,hn.ne']
  have heU : e ∈ U := U.smul_mem _ hh
  have hpF : β • e+y ∈ affineSpan ℝ (exclusion C₁ u₁ p) :=
    (affineSpan ℝ (exclusion C₁ u₁ p)).vadd_mem_of_mem_direction (U.smul_mem _ heU) hy
  have hmF : (-β) • e+y ∈ affineSpan ℝ (exclusion C₁ u₁ p) :=
    (affineSpan ℝ (exclusion C₁ u₁ p)).vadd_mem_of_mem_direction (U.smul_mem _ heU) hy
  have hpB : β • e+y ∈ Metric.closedBall y β := by simp [Metric.mem_closedBall,dist_eq_norm,norm_smul,he,abs_of_pos hβ]
  have hmB : (-β) • e+y ∈ Metric.closedBall y β := by simp [Metric.mem_closedBall,dist_eq_norm,norm_smul,he,abs_of_pos hβ]
  obtain ⟨xp,hxp,hxpπ⟩ := hball ⟨hpB,hpF⟩
  obtain ⟨xm,hxm,hxmπ⟩ := hball ⟨hmB,hmF⟩
  obtain ⟨vp,hvp,rfl⟩ := c.whole.symm ▸ hxp
  obtain ⟨vm,hvm,rfl⟩ := c.whole.symm ▸ hxm
  have hvp1 : ‖vp‖ ≤ 1 := by simpa using hvp
  have hvm1 : ‖vm‖ ≤ 1 := by simpa using hvm
  have hd : U.starProjection (c.param.linear (vp-vm)) = (2*β) • e := by
    have h := (sourceProjection p a).linear_apply_vsub (c.param vp) (c.param vm)
    rw [sourceProjection_linear,hxpπ,hxmπ] at h
    rw [← c.param.linear_apply_vsub,vsub_eq_sub] at h
    change U.starProjection (c.param.linear (vp-vm)) = _ at h
    change U.starProjection (c.param.linear (vp-vm)) = β • e+y-((-β) • e+y) at h
    rw [h]
    module
  have hhP : U.starProjection h = h := Submodule.starProjection_eq_self_iff.mpr hh
  have heinner : ⟪h,e⟫ = ‖h‖ := by
    simp only [e,inner_smul_right,real_inner_self_eq_norm_sq]
    field_simp
  have hvdiff : ‖vp-vm‖ ≤ 2 := (norm_sub_le vp vm).trans (by linarith)
  have hcs := real_inner_le_norm (c.param.linear.toContinuousLinearMap.adjoint h) (vp-vm)
  have heq : ⟪c.param.linear.toContinuousLinearMap.adjoint h,vp-vm⟫ = 2*β*‖h‖ := by
    calc
      _ = ⟪h,c.param.linear (vp-vm)⟫ := ContinuousLinearMap.adjoint_inner_left _ _ _
      _ = ⟪U.starProjection h,c.param.linear (vp-vm)⟫ := by rw [hhP]
      _ = ⟪h,U.starProjection (c.param.linear (vp-vm))⟫ := U.inner_starProjection_left_eq_right _ _
      _ = _ := by rw [hd,inner_smul_right,heinner]
  rw [heq] at hcs
  have hh2 := mul_le_mul_of_nonneg_left hvdiff (norm_nonneg (c.param.linear.toContinuousLinearMap.adjoint h))
  linarith

private theorem actual_singular_bounds
    (hc : IsClosed (C₁ : Set E)) (hs : ∀ x ∈ C₁, x ≠ 0 → 0 < u₁ x)
    (hg : Submodule.span ℝ (C₁ : Set E) = ⊤) (hB : exclusionBalls C₁ u₁)
    (p t : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p) (c : ExclusionChart C₁ u₁ t)
    {y : E} (hy : y ∈ affineSpan ℝ (exclusion C₁ u₁ p)) {β : ℝ} (hβ : 0 < β)
    (hd : a.dim+1 ≤ c.dim)
    (hball : Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
      sourceProjection p a '' exclusion C₁ u₁ t)
    {z : EuclideanSpace ℝ (Fin c.dim)} (hz : ‖z‖ = 1) :
    β ≤ c.param.linear.singularValues (a.dim-1) ∧
    c.param.linear.singularValues a.dim ≤ leakage C₁ u₁ p t ∧
    ‖(projectedLinear p c).ker.starProjection z‖ ≤
      ‖(singularTail c.param.linear.toContinuousLinearMap a.dim).starProjection z‖+
        leakage C₁ u₁ p t/β := by
  let U := (affineSpan ℝ (exclusion C₁ u₁ p)).direction
  let L := c.param.linear.toContinuousLinearMap
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin c.dim)) = c.dim := by simp
  have hα : 0 ≤ leakage C₁ u₁ p t := by
    obtain ⟨x,hx⟩ := ((exclusion_ball_faces hc hs hg hB).1 t).1.nonempty
    exact Metric.infDist_nonneg.trans (leakage_point_le hc hs hg hB p t hx)
  have herr (x) : ‖Uᗮ.starProjection (L x)‖ ≤ leakage C₁ u₁ p t*‖x‖ :=
    ((Uᗮ.starProjection.comp L).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (normal_operator_bound hc hs hg hB p t a c) (norm_nonneg x))
  have hkept := kept_of_dual_coercive L U (chart_dimension a) a.dim_pos
    (by rw [hdim]; omega) hβ (projected_ball_dual_bound p t a c hy hβ hball)
  have hthin := thin_of_projected_error L U (chart_dimension a)
    (by rw [hdim]; omega) hα herr
  refine ⟨hkept,hthin,?_⟩
  rw [singularTail_eq]
  apply projection_mass_transfer _ _ (div_nonneg hα hβ.le) _ hz
  intro v hv
  have hAv : U.starProjection (L v) = 0 := by
    have hh := hv
    change projectedLinear p c v = 0 at hh
    exact congrArg (fun w : U => (w:E)) hh
  have he := U.starProjection_add_starProjection_orthogonal (L v)
  rw [hAv,zero_add] at he
  have hLv : ‖L v‖ ≤ leakage C₁ u₁ p t*‖v‖ := by simpa only [he] using herr v
  have hlead := leading_projection_bound L a.dim_pos (by rw [hdim]; omega) v
  have hh := mul_le_mul_of_nonneg_right hkept (norm_nonneg ((leading L a.dim).starProjection v))
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hβ).mpr (by nlinarith)

private theorem tail_mass_from_margin {R β e q w α : ℝ}
    (hR : 0 < R) (hβ : 0 < β) (hβR : β < R) (he : 0 ≤ e) (heβ : e < β/2)
    (hq : 0 ≤ q) (hw : 0 ≤ w) (_hw1 : w ≤ 1) (_hα : 0 ≤ α)
    (hmargin : 1-(1-(β-e)/R)^2 ≤ q^2)
    (htransfer : q ≤ w+α/β)
    (hsmall : α/β < Real.sqrt (1-(1-β/(2*R))^2)/2) :
    (1-(1-β/(2*R))^2)/4 ≤ w^2 := by
  let γ := 1-(1-β/(2*R))^2
  have hm : 0 < β/(2*R) := div_pos hβ (by positivity)
  have hm1 : β/(2*R) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hγ : 0 < γ := by dsimp [γ]; nlinarith
  have hratio : β/(2*R) ≤ (β-e)/R := by
    rw [le_div_iff₀ hR]
    field_simp
    nlinarith
  have hratio1 : (β-e)/R ≤ 1 := (div_le_one hR).mpr (by linarith)
  have hγq : γ ≤ q^2 := by dsimp [γ]; nlinarith
  have hs := Real.sq_sqrt hγ.le
  have hs0 := Real.sqrt_nonneg γ
  have hsq : Real.sqrt γ ≤ q := by nlinarith
  have htail : Real.sqrt γ/2 ≤ w := by dsimp [γ] at hsq hs0 ⊢; linarith
  nlinarith

/-- Fixed original sectors force dimension escape and an actual projected
inner ball for every sequence satisfying the additional common-sector condition.
The singular estimates and tail transfer are supplied by the spectral lemmas. -/
private theorem projected_return_geometry
    (hc : IsClosed (C₁ : Set E)) (hs : ∀ x ∈ C₁, x ≠ 0 → 0 < u₁ x)
    (hg : Submodule.span ℝ (C₁ : Set E) = ⊤) (hB : exclusionBalls C₁ u₁)
    (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {y : E} (hy : y ∈ intrinsicInterior ℝ (exclusion C₁ u₁ p))
    (ξ : EuclideanSpace ℝ (Fin a.dim)) (hξ : a.param ξ = y)
    (b : AffineBasis (Fin (a.dim+1)) ℝ (EuclideanSpace ℝ (Fin a.dim)))
    (hb : ∀ i, ‖b i‖ = 1) (hpos : ∀ i, 0 < b.coord i ξ) :
    ∃ ε θ H β : ℝ, 0 < ε ∧ 0 < θ ∧ 0 < H ∧ 0 < β ∧
      β < Metric.diam (base C₁ u₁)/2 ∧
      (∀ r t : pure C₁ u₁, dist (r:E) y < ε → (t:E) ∈ exclusion C₁ u₁ r →
        Module.finrank ℝ (affineSpan ℝ (exclusion C₁ u₁ t)).direction ≤ a.dim →
        ∃ i : Fin (a.dim+1), ∀ f : E →L[ℝ] ℝ,
          f ≠ 0 → (∀ x ∈ C₁, 0 ≤ f x) → f t = 0 → slope a f ≠ 0 →
          ‖‖slope a f‖⁻¹ • slope a f - b i‖ < θ →
          ‖slope a f‖ ≤ H*baseMaximum C₁ u₁ f*leakage C₁ u₁ p t) ∧
      ∀ (r t : ℕ → pure C₁ u₁), Tendsto (fun n => (r n:E)) atTop (𝓝 y) →
        (∀ n, (t n:E) ∈ exclusion C₁ u₁ (r n)) →
        (∀ᶠ n in atTop, sectorViolation a b (t n) θ H) →
        ∀ (c : ∀ n, ExclusionChart C₁ u₁ (t n))
          (z : ∀ n, EuclideanSpace ℝ (Fin (c n).dim)),
          (∀ n, (c n).param (z n) = r n) →
          Tendsto (fun n => leakage C₁ u₁ p (t n)) atTop (𝓝 0) ∧
          (∀ n, ‖z n‖ = 1 ∧ 0 < (c n).dim ∧
            (c n).dim ≤ Module.finrank ℝ (LinearMap.ker u₁) ∧
            ‖(c n).param.linear.toContinuousLinearMap‖ ≤ Metric.diam (base C₁ u₁)/2) ∧
          ∀ᶠ n in atTop, a.dim+1 ≤ (c n).dim ∧
            Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
              sourceProjection p a '' exclusion C₁ u₁ (t n) ∧
            1-(1-(β-dist (r n:E) y)/(Metric.diam (base C₁ u₁)/2))^2 ≤
              ‖(projectedLinear p (c n)).ker.starProjection (z n)‖^2 := by
  classical
  obtain ⟨ε₀,θ₀,H₀,hε₀,hθ₀,hH₀,hsector⟩ := uniform_return_sectors hc hs hg hB p a hy ξ hξ b hb hpos
  obtain ⟨δ,β₀,hδ,hβ₀,hball⟩ := projected_simplex_ball p a ξ hξ b hb hpos
  obtain ⟨θ₁,H₁,hθ₁,hH₁,hcontact⟩ := sector_contact_family hc hs hg hB p a b hδ
  obtain ⟨ε₁,hε₁,hleak⟩ := whole_return_leakage hc hs hg hB p hy (by positivity : 0 < δ/4)
  let θ := min θ₀ θ₁
  let H := max H₀ H₁
  let β := min β₀ (Metric.diam (base C₁ u₁)/4)
  have hR := base_radius_positive hc hs p a
  have hβ : 0 < β := lt_min hβ₀ (by linarith)
  have hβR : β < Metric.diam (base C₁ u₁)/2 := (min_le_right _ _).trans_lt (by linarith)
  have hα0 (t : pure C₁ u₁) : 0 ≤ leakage C₁ u₁ p t := by
    obtain ⟨x,hx⟩ := ((exclusion_ball_faces hc hs hg hB).1 t).1.nonempty
    exact Metric.infDist_nonneg.trans (leakage_point_le hc hs hg hB p t hx)
  have hM0 (t : pure C₁ u₁) (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
      (hp : ∀ x ∈ C₁, 0 ≤ f x) (ht : f t = 0) : 0 ≤ baseMaximum C₁ u₁ f := by
    obtain ⟨A,_,h⟩ := uniform_dual_bound hc hs hg
    exact (h t f hf hp ht).1.le
  have hsector' : ∀ r t : pure C₁ u₁, dist (r:E) y < min ε₀ ε₁ →
      (t:E) ∈ exclusion C₁ u₁ r →
      Module.finrank ℝ (affineSpan ℝ (exclusion C₁ u₁ t)).direction ≤ a.dim →
      ∃ i : Fin (a.dim+1), ∀ f : E →L[ℝ] ℝ,
        f ≠ 0 → (∀ x ∈ C₁, 0 ≤ f x) → f t = 0 → slope a f ≠ 0 →
        ‖‖slope a f‖⁻¹ • slope a f - b i‖ < θ →
        ‖slope a f‖ ≤ H*baseMaximum C₁ u₁ f*leakage C₁ u₁ p t := by
    intro r t hr ht hd
    obtain ⟨i,hi⟩ := hsector r t (hr.trans_le (min_le_left _ _)) ht hd
    refine ⟨i,fun f hf hp hft hfg hdir => ?_⟩
    exact (hi f hf hp hft hfg (hdir.trans_le (min_le_left _ _))).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (hM0 t f hf hp hft)) (hα0 t))
  refine ⟨min ε₀ ε₁,θ,H,β,lt_min hε₀ hε₁,lt_min hθ₀ hθ₁,
    hH₀.trans_le (le_max_left _ _),hβ,hβR,hsector',fun r t hr ht hfail c z hz => ?_⟩
  refine ⟨actual_leakage_tendsto hc hs hg hB p hy r t hr ht,
    fun n => ⟨actual_parameter_unit hc hs hg hB (r n) (t n) (ht n) (c n) (z n) (hz n),
      (c n).dim_pos,chart_dimension_bound (c n),chart_operator_bound hc hs (c n)⟩,?_⟩
  filter_upwards [hfail,Metric.tendsto_nhds.mp hr (min (min ε₀ ε₁) β)
    (lt_min (lt_min hε₀ hε₁) hβ)] with n hn hnear₀
  have hnear := hnear₀.trans_le (min_le_left _ _)
  have hnearβ := hnear₀.trans_le (min_le_right _ _)
  have hfail₁ : sectorViolation a b (t n) θ₁ H₁ := by
    intro i
    obtain ⟨f,hf,hp,hft,hfg,hdir,hbig⟩ := hn i
    refine ⟨f,hf,hp,hft,hfg,hdir.trans_le (min_le_right _ _),?_⟩
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (hM0 (t n) f hf hp hft)) (hα0 (t n))).trans_lt hbig
  have hdim : a.dim+1 ≤ (c n).dim := by
    by_contra! hd
    have hd' : Module.finrank ℝ (affineSpan ℝ (exclusion C₁ u₁ (t n))).direction ≤ a.dim := by
      rw [chart_dimension (c n)]; omega
    obtain ⟨i,hi⟩ := hsector' (r n) (t n) hnear (ht n) hd'
    obtain ⟨f,hf,hp,hft,hfg,hdir,hbig⟩ := hn i
    exact hbig.not_ge (hi f hf hp hft hfg hdir)
  have hreturnball : Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
      sourceProjection p a '' exclusion C₁ u₁ (t n) := by
    obtain ⟨x,hx⟩ := hcontact (t n) (hleak (r n) (t n) (hnear.trans_le (min_le_right _ _)) (ht n)) hfail₁
    have hinside : convexHull ℝ (range (fun i => sourceProjection p a (x i:E))) ⊆
        sourceProjection p a '' exclusion C₁ u₁ (t n) :=
      convexHull_min (by rintro _ ⟨i,rfl⟩; exact mem_image_of_mem _ (hx i).1)
        (((exclusion_ball_faces hc hs hg hB).1 (t n)).2.2.1.affine_image (sourceProjection p a))
    intro q hq
    apply hinside
    apply hball (fun i => (x i:E)) (fun i => (hx i).2)
    exact ⟨Metric.closedBall_subset_closedBall (min_le_left _ _) hq.1,hq.2⟩
  exact ⟨hdim,hreturnball,actual_projected_margin hc hs hg hB p a
    (subset_affineSpan ℝ _ (intrinsicInterior_subset hy)) hβ hβR
    (r n) (t n) (ht n) (c n) (z n) (hz n) hnearβ hreturnball⟩

/-- Complete original common-sector return conclusion, with fixed kept singular value
and positive mass in the ordered right singular tail. -/
theorem original_return_geometry
    (hc : IsClosed (C₁ : Set E)) (hs : ∀ x ∈ C₁, x ≠ 0 → 0 < u₁ x)
    (hg : Submodule.span ℝ (C₁ : Set E) = ⊤) (hB : exclusionBalls C₁ u₁)
    (p : pure C₁ u₁) (a : ExclusionChart C₁ u₁ p)
    {y : E} (hy : y ∈ intrinsicInterior ℝ (exclusion C₁ u₁ p))
    (ξ : EuclideanSpace ℝ (Fin a.dim)) (hξ : a.param ξ = y)
    (b : AffineBasis (Fin (a.dim+1)) ℝ (EuclideanSpace ℝ (Fin a.dim)))
    (hb : ∀ i, ‖b i‖ = 1) (hpos : ∀ i, 0 < b.coord i ξ) :
    ∃ ε θ H β η : ℝ, 0 < ε ∧ 0 < θ ∧ 0 < H ∧ 0 < β ∧ 0 < η ∧
      β < Metric.diam (base C₁ u₁)/2 ∧
      (∀ r t : pure C₁ u₁, dist (r:E) y < ε → (t:E) ∈ exclusion C₁ u₁ r →
        Module.finrank ℝ (affineSpan ℝ (exclusion C₁ u₁ t)).direction ≤ a.dim →
        ∃ i : Fin (a.dim+1), ∀ f : E →L[ℝ] ℝ,
          f ≠ 0 → (∀ x ∈ C₁, 0 ≤ f x) → f t = 0 → slope a f ≠ 0 →
          ‖‖slope a f‖⁻¹ • slope a f - b i‖ < θ →
          ‖slope a f‖ ≤ H*baseMaximum C₁ u₁ f*leakage C₁ u₁ p t) ∧
      ∀ (r t : ℕ → pure C₁ u₁), Tendsto (fun n => (r n:E)) atTop (𝓝 y) →
        (∀ n, (t n:E) ∈ exclusion C₁ u₁ (r n)) →
        (∀ᶠ n in atTop, sectorViolation a b (t n) θ H) →
        ∀ (c : ∀ n, ExclusionChart C₁ u₁ (t n))
          (z : ∀ n, EuclideanSpace ℝ (Fin (c n).dim)),
          (∀ n, (c n).param (z n) = r n) →
          Tendsto (fun n => leakage C₁ u₁ p (t n)) atTop (𝓝 0) ∧
          (∀ n, ‖z n‖ = 1 ∧ 0 < (c n).dim ∧
            (c n).dim ≤ Module.finrank ℝ (LinearMap.ker u₁) ∧
            ‖(c n).param.linear.toContinuousLinearMap‖ ≤ Metric.diam (base C₁ u₁)/2) ∧
          (∀ᶠ n in atTop, a.dim+1 ≤ (c n).dim ∧
            Metric.closedBall y β ∩ (affineSpan ℝ (exclusion C₁ u₁ p) : Set E) ⊆
              sourceProjection p a '' exclusion C₁ u₁ (t n) ∧
            1-(1-(β-dist (r n:E) y)/(Metric.diam (base C₁ u₁)/2))^2 ≤
              ‖(projectedLinear p (c n)).ker.starProjection (z n)‖^2 ∧
            β ≤ (c n).param.linear.singularValues (a.dim-1) ∧
            (c n).param.linear.singularValues a.dim ≤ leakage C₁ u₁ p (t n)) ∧
          β ≤ liminf (fun n => (c n).param.linear.singularValues (a.dim-1)) atTop ∧
          η ≤ liminf (fun n => ‖(singularTail (c n).param.linear.toContinuousLinearMap a.dim).starProjection (z n)‖^2) atTop := by
  classical
  obtain ⟨ε,θ,H,β,hε,hθ,hH,hβ,hβR,hsector,hgeometry⟩ :=
    projected_return_geometry hc hs hg hB p a hy ξ hξ b hb hpos
  let R := Metric.diam (base C₁ u₁)/2
  let γ := 1-(1-β/(2*R))^2
  have hR : 0 < R := base_radius_positive hc hs p a
  have hm : 0 < β/(2*R) := div_pos hβ (by positivity)
  have hm1 : β/(2*R) < 1 := (div_lt_one (by positivity)).mpr (by dsimp [R]; linarith)
  have hγ : 0 < γ := by dsimp [γ]; nlinarith
  refine ⟨ε,θ,H,β,γ/4,hε,hθ,hH,hβ,by positivity,hβR,hsector,?_⟩
  intro r t hr ht hfail c z hz
  obtain ⟨hleak,hunit,hgeom⟩ := hgeometry r t hr ht hfail c z hz
  have hspec : ∀ᶠ n in atTop,
      β ≤ (c n).param.linear.singularValues (a.dim-1) ∧
      (c n).param.linear.singularValues a.dim ≤ leakage C₁ u₁ p (t n) ∧
      ‖(projectedLinear p (c n)).ker.starProjection (z n)‖ ≤
        ‖(singularTail (c n).param.linear.toContinuousLinearMap a.dim).starProjection (z n)‖+
          leakage C₁ u₁ p (t n)/β := by
    filter_upwards [hgeom] with n hn
    exact actual_singular_bounds hc hs hg hB p (t n) a (c n)
      (subset_affineSpan ℝ _ (intrinsicInterior_subset hy)) hβ hn.1 hn.2.1 (hunit n).1
  have hnorm (n) : ‖(singularTail (c n).param.linear.toContinuousLinearMap a.dim).starProjection (z n)‖ ≤ 1 :=
    ((singularTail (c n).param.linear.toContinuousLinearMap a.dim).norm_starProjection_apply_le (z n)).trans_eq (hunit n).1
  have hmass : ∀ᶠ n in atTop,
      γ/4 ≤ ‖(singularTail (c n).param.linear.toContinuousLinearMap a.dim).starProjection (z n)‖^2 := by
    have hsmall : ∀ᶠ n in atTop, leakage C₁ u₁ p (t n)/β < Real.sqrt γ/2 :=
      (tendsto_order.mp (hleak.div_const β)).2 _ (by simp only [zero_div]; positivity)
    filter_upwards [hgeom,hspec,Metric.tendsto_nhds.mp hr (β/2) (by positivity),hsmall]
      with n hn hspectral hnear hsmall
    have hα : 0 ≤ leakage C₁ u₁ p (t n) := by
      obtain ⟨x,hx⟩ := ((exclusion_ball_faces hc hs hg hB).1 (t n)).1.nonempty
      exact Metric.infDist_nonneg.trans (leakage_point_le hc hs hg hB p (t n) hx)
    exact tail_mass_from_margin hR hβ hβR dist_nonneg hnear (norm_nonneg _) (norm_nonneg _)
      (hnorm n) hα hn.2.2 hspectral.2.2 hsmall
  refine ⟨hleak,hunit,?_,?_,?_⟩
  · filter_upwards [hgeom,hspec] with n hn hspectral
    exact ⟨hn.1,hn.2.1,hn.2.2,hspectral.1,hspectral.2.1⟩
  · apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun n =>
      (singular_le_norm (c n).param.linear.toContinuousLinearMap (a.dim-1)).trans (hunit n).2.2.2))
    exact hspec.mono fun _ hn => hn.1
  · apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun n =>
      show ‖(singularTail (c n).param.linear.toContinuousLinearMap a.dim).starProjection (z n)‖^2 ≤ 1 from by
        nlinarith [hnorm n,norm_nonneg ((singularTail (c n).param.linear.toContinuousLinearMap a.dim).starProjection (z n))]))
    exact hmass

end EuclideanReturns
end D5.S3.Quantum.Foundation.OriginalReturnSectors
