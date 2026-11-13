/- GID: D5/S3/Quantum/Foundation/OriginalReturnSectors/LinearGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalReturnSectors/LinearGeometry
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Ordered real singular estimates and projected-kernel minimum-norm margins. -/

import D5.S3.Quantum.Foundation.SingleLabelNormalBody
import D5.S3.Quantum.Foundation.MixedExclusionGeometry
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Analysis.Normed.Affine.Convex


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
def leading (L : X →L[ℝ] Y) (k : ℕ) : Submodule ℝ X :=
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

theorem leading_projection_bound (L : X →L[ℝ] Y) {k : ℕ}
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

theorem thin_of_projected_error (L : X →L[ℝ] Y) (U : Submodule ℝ Y)
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

theorem kept_of_dual_coercive (L : X →L[ℝ] Y) (U : Submodule ℝ Y)
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

theorem singularTail_eq (L : X →L[ℝ] Y) (k : ℕ) :
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

theorem singular_le_norm (L : X →L[ℝ] Y) (i : ℕ) :
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

theorem kernel_margin (A : E →L[ℝ] F) {R ρ : ℝ}
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


theorem projection_mass_transfer (J T : Submodule ℝ E) {ε : ℝ}
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

end D5.S3.Quantum.Foundation.OriginalReturnSectors
