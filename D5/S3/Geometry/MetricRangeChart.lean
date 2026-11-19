/- GID: D5/S3/Geometry/MetricRangeChart
   generality: G
   mirror-B: D5/B/S3/Geometry/MetricRangeChart
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Positive range metrics give continuous normalized linear charts and exact local disc products. -/
import D5.S3.Geometry.ContinuousRangeBundle
import D5.S3.Geometry.EllipsoidShape

/-! Normalization preserves the actual subspace fibers and their ambient topology. -/


noncomputable section
open Set Metric Topology
open scoped InnerProductSpace
namespace D5.S3.Geometry.ContinuousRangeBundle
variable {X E H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  {S : X → Submodule ℝ H}

structure NormalizedChart (S : X → Submodule ℝ H) (B : X → H →L[ℝ] H)
    extends Chart (E := E) S where
  metric_preserving : ∀ x ∈ U, ∀ v w : E,
    ⟪forward x v, B x (forward x w)⟫_ℝ = ⟪v, w⟫_ℝ

/-- A positive metric on the actual range normalizes local linear charts continuously. -/
theorem exists_normalized_chart (a : Chart (E := E) S) (B : X → H →L[ℝ] H)
    (hB : Continuous B) (hp : ∀ x, (B x).IsPositive)
    (hd : ∀ x v, v ∈ S x → v ≠ 0 → 0 < ⟪v, B x v⟫_ℝ) :
    ∃ b : NormalizedChart (E := E) S B, b.U = a.U := by
  classical
  let M (x : X) := (a.forward x).adjoint.comp ((B x).comp (a.forward x))
  have hMpos (x : X) : (M x).IsPositive := (hp x).adjoint_conj (a.forward x)
  have hM : ContinuousOn M a.U := by
    have hadj : ContinuousOn (fun x => (a.forward x).adjoint) a.U :=
      ContinuousLinearMap.adjoint.continuous.comp_continuousOn a.continuousOn_forward
    exact hadj.clm_comp (hB.continuousOn.clm_comp a.continuousOn_forward)
  let T (x : X) := D5.S3.Geometry.EllipsoidShape.positiveSqrt (M x)
  have hT : ContinuousOn T a.U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact D5.S3.Geometry.EllipsoidShape.continuous_positiveSqrt
      (fun x : a.U => M x) (continuousOn_iff_continuous_domRestrict.mp hM)
      (fun x => hMpos x)
  have hTspec (x : X) := D5.S3.Geometry.EllipsoidShape.positiveSqrt_spec (M x) (hMpos x)
  have hMi (x : X) (hx : x ∈ a.U) : Function.Injective (M x) := by
    apply (injective_iff_map_eq_zero (M x)).mpr
    intro v hv
    have hFi : Function.Injective (a.forward x) := by
      intro v w he
      have hl := congrArg (fun A : E →L[ℝ] E => A v) (a.left_inverse x hx)
      have hr := congrArg (fun A : E →L[ℝ] E => A w) (a.left_inverse x hx)
      change a.backward x (a.forward x v) = v at hl
      change a.backward x (a.forward x w) = w at hr
      rw [← hl, ← hr, he]
    by_contra hn
    have hnF : a.forward x v ≠ 0 := by
      intro hz
      exact hn (hFi (by simpa using hz))
    have hh := hd x (a.forward x v) (a.mem_range x v) hnF
    have he : ⟪a.forward x v, B x (a.forward x v)⟫_ℝ = 0 := by
      rw [real_inner_comm, ← (a.forward x).adjoint_inner_left]
      change ⟪M x v, v⟫_ℝ = 0
      rw [hv, inner_zero_left]
    linarith
  have hTi (x : X) (hx : x ∈ a.U) : Function.Injective (T x) := by
    apply (injective_iff_map_eq_zero (T x)).mpr
    intro v hv
    apply (hMi x hx)
    rw [map_zero]
    have he := congrArg (fun A : E →L[ℝ] E => A v) (hTspec x).2.1
    change T x (T x v) = M x v at he
    rw [hv, map_zero] at he
    exact he.symm
  have hTinv (x : X) (hx : x ∈ a.U) : (T x).IsInvertible := by
    let e := LinearEquiv.ofBijective (T x).toLinearMap
      ⟨hTi x hx, LinearMap.injective_iff_surjective.mp (hTi x hx)⟩
    exact ⟨e.toContinuousLinearEquiv, rfl⟩
  have hInv : ContinuousOn (fun x => (T x).inverse) a.U := by
    intro x hx
    have hu : IsUnit (T x) := ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hTi x hx, LinearMap.injective_iff_surjective.mp (hTi x hx)⟩
    obtain ⟨v, hv⟩ := hu
    rw [← ContinuousLinearMap.ringInverse_eq_inverse]
    exact (hv ▸ NormedRing.inverse_continuousAt v).comp_continuousWithinAt (hT x hx)
  let b : Chart (E := E) S := {
    U := a.U
    open_U := a.open_U
    forward x := (a.forward x).comp (T x).inverse
    backward x := (T x).comp (a.backward x)
    continuousOn_forward := a.continuousOn_forward.clm_comp hInv
    continuousOn_backward := hT.clm_comp a.continuousOn_backward
    mem_range x v := a.mem_range x _
    left_inverse x hx := by
      ext v
      change T x (a.backward x (a.forward x ((T x).inverse v))) = v
      have he := congrArg (fun A : E →L[ℝ] E => A ((T x).inverse v)) (a.left_inverse x hx)
      change a.backward x (a.forward x ((T x).inverse v)) = (T x).inverse v at he
      rw [he, (hTinv x hx).self_apply_inverse]
    right_inverse x hx v hv := by
      change a.forward x ((T x).inverse (T x (a.backward x v))) = v
      rw [(hTinv x hx).inverse_apply_self]
      exact a.right_inverse x hx v hv }
  refine ⟨{ b with metric_preserving := ?_ }, rfl⟩
  intro x hx v w
  change ⟪a.forward x ((T x).inverse v), B x (a.forward x ((T x).inverse w))⟫_ℝ = ⟪v, w⟫_ℝ
  rw [← (a.forward x).adjoint_inner_right]
  change ⟪(T x).inverse v, M x ((T x).inverse w)⟫_ℝ = ⟪v, w⟫_ℝ
  rw [← (hTspec x).2.1]
  change ⟪(T x).inverse v, T x (T x ((T x).inverse w))⟫_ℝ = ⟪v, w⟫_ℝ
  rw [(hTinv x hx).self_apply_inverse,
    ← (hTspec x).1.inner_left_eq_inner_right,
    (hTinv x hx).self_apply_inverse]
namespace NormalizedChart
variable {B : X → H →L[ℝ] H} (a : NormalizedChart (E := E) S B)
private theorem metric_coords (x : X) (hx : x ∈ a.U) (v : H) (hv : v ∈ S x) :
    ⟪v, B x v⟫_ℝ = ‖a.backward x v‖ ^ 2 := by
  have he := a.metric_preserving x hx (a.backward x v) (a.backward x v)
  rw [a.right_inverse x hx v hv, real_inner_self_eq_norm_sq] at he
  exact he

private def levelHomeomorph (r : ℝ → Prop) :
    {z : X × H // z.1 ∈ a.U ∧ z.2 ∈ S z.1 ∧ r ⟪z.2, B z.1 z.2⟫_ℝ} ≃ₜ
      (a.U × {v : E // r (‖v‖ ^ 2)}) := by
  let D := {z : X × H // z.1 ∈ a.U ∧ z.2 ∈ S z.1 ∧ r ⟪z.2, B z.1 z.2⟫_ℝ}
  let f (z : D) : a.U × {v : E // r (‖v‖ ^ 2)} :=
    (⟨z.1.1, z.2.1⟩, ⟨a.backward z.1.1 z.1.2, by
      rw [← a.metric_coords z.1.1 z.2.1 z.1.2 z.2.2.1]
      exact z.2.2.2⟩)
  let g (z : a.U × {v : E // r (‖v‖ ^ 2)}) : D :=
    ⟨(z.1, a.forward z.1 z.2), z.1.property, a.mem_range z.1 z.2, by
      rw [a.metric_preserving z.1 z.1.property, real_inner_self_eq_norm_sq]
      exact z.2.property⟩
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · intro z
    apply Subtype.ext
    exact Prod.ext rfl (a.right_inverse z.1.1 z.2.1 z.1.2 z.2.2.1)
  · intro z
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact congrArg (fun T : E →L[ℝ] E => T z.2) (a.left_inverse z.1 z.1.property)
  · have hb : Continuous (fun z : D => (⟨z.1.1, z.2.1⟩ : a.U)) :=
      (continuous_fst.comp continuous_subtype_val).subtype_mk _
    have hc : Continuous (fun z : D => a.backward z.1.1 z.1.2) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      have hbase : ContinuousAt (fun z : D => z.1.1) z :=
        (continuous_fst.comp continuous_subtype_val).continuousAt
      have hvec : ContinuousAt (fun z : D => z.1.2) z :=
        (continuous_snd.comp continuous_subtype_val).continuousAt
      have hback : ContinuousAt (fun z : D => a.backward z.1.1) z :=
        ContinuousAt.comp (f := fun z : D => z.1.1) (x := z)
          (a.continuousOn_backward.continuousAt (a.open_U.mem_nhds z.2.1)) hbase
      exact hback.clm_apply hvec
    exact hb.prodMk (hc.subtype_mk _)
  · have hb : Continuous (fun z : a.U × {v : E // r (‖v‖ ^ 2)} => (z.1 : X)) :=
      continuous_subtype_val.comp continuous_fst
    have hv : Continuous (fun z : a.U × {v : E // r (‖v‖ ^ 2)} =>
        a.forward z.1 z.2) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      have hfor : ContinuousAt (fun z : a.U × {v : E // r (‖v‖ ^ 2)} =>
          a.forward z.1) z :=
        ContinuousAt.comp (f := fun z : a.U × {v : E // r (‖v‖ ^ 2)} => (z.1 : X)) (x := z)
          (a.continuousOn_forward.continuousAt (a.open_U.mem_nhds z.1.property)) hb.continuousAt
      exact hfor.clm_apply (continuous_subtype_val.comp continuous_snd).continuousAt
    exact (hb.prodMk hv).subtype_mk _

/-- The actual range-restricted closed unit disc has a continuous normalized local product. -/
def discHomeomorph :
    {z : X × H // z.1 ∈ a.U ∧ z.2 ∈ S z.1 ∧ ⟪z.2, B z.1 z.2⟫_ℝ ≤ 1} ≃ₜ
      (a.U × closedBall (0 : E) 1) :=
  (a.levelHomeomorph (· ≤ 1)).trans ((Homeomorph.refl a.U).prodCongr
    (Homeomorph.setCongr (by
      ext v
      rw [mem_closedBall_zero_iff]
      change ‖v‖ ^ 2 ≤ 1 ↔ ‖v‖ ≤ 1
      constructor <;> intro h <;> nlinarith [norm_nonneg v])))

/-- Its actual unit sphere has the corresponding continuous normalized local product. -/
def sphereHomeomorph :
    {z : X × H // z.1 ∈ a.U ∧ z.2 ∈ S z.1 ∧ ⟪z.2, B z.1 z.2⟫_ℝ = 1} ≃ₜ
      (a.U × sphere (0 : E) 1) :=
  (a.levelHomeomorph (· = 1)).trans ((Homeomorph.refl a.U).prodCongr
    (Homeomorph.setCongr (by
      ext v
      rw [mem_sphere_zero_iff_norm]
      change ‖v‖ ^ 2 = 1 ↔ ‖v‖ = 1
      constructor <;> intro h <;> nlinarith [norm_nonneg v])))
end NormalizedChart

end D5.S3.Geometry.ContinuousRangeBundle
