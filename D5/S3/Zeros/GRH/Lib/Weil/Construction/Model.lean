/- GID: D5/S3/Zeros/GRH/Lib/Weil/Construction/Model
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Construction/Model
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Construction.Model. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Construction/Model.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Construction.SubmoduleNormedSpace
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.HaarUnique
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: L¹ (Feichtinger) space of vacuum coefficients, Heisenberg representation, reproducing
formula, Schur's lemma. -/

noncomputable section

open MeasureTheory ComplexConjugate Subtype LinearMap DFunLike

namespace Heisenberg

variable {W : Type _} [AddCommGroup W] [TopologicalSpace W] (H : Heisenberg W) [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] {μ : Measure W}
  [μ.IsAddHaarMeasure] {e : W → ℂ} [he : IsVacuum H μ e] {X : Type _} [NormedAddCommGroup X]
  [NormedSpace ℂ X] {Y : Type _} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
attribute [local simp] mul_le_of_le_one_right norm_smul mul_le_mul add_left add_right integral_add
  norm_integral_le_of_norm_le Integrable.norm smul_smul

omit [μ.IsAddHaarMeasure] in
lemma IsVacuum.integrable_mul_kernel x {f} : Integrable f μ → Integrable (fun y ↦
  f y * (H.β y x * e (x - y))) μ := (·.mono (he.rec (by fun_prop)) (by simp [he.norm_le_one]))

/-- The complex subspace of integrable functions v on W satisfying the reproducing identity v(x)
= ∫ v(y) β(y,x) e(x−y) dμ(y) for every x. -/
def IsVacuum.modelSubmodule : Submodule ℂ (W → ℂ) := by
  use! {v | Integrable v μ ∧ ∀ x, ∫ y, v y * (H.β y x * e (x - y)) ∂μ = v x} <;> simp_all
    [add_mul, integrable_mul_kernel, mul_assoc, Integrable.smul]

/-- The space of integrable v with v(x) = ∫ v(y) β(y,x) e(x−y) dμ(y), as a type; it carries the
L¹ norm. -/
def IsVacuum.Model := ↥he.modelSubmodule

deriving instance AddCommGroup, Module ℂ for (he.Model)

instance : CoeFun he.Model fun _ ↦ W → ℂ := ⟨val⟩

/-- The complex-linear map sending a function in the reproducing space to its class in L¹(W, μ). -/
def IsVacuum.toL1 : he.Model →ₗ[ℂ] W →₁[μ] ℂ := by use! (·.2.1.toL1) <;> tauto

instance : NormedAddCommGroup he.Model := .induced _ _ he.toL1 fun v w h ↦ Subtype.ext (funext
  (v.2.2 · ▸ w.2.2 _ ▸ integral_congr_ae (.mul_right (by simp_all [IsVacuum.toL1, coe]))))

instance : NormedSpace ℂ he.Model := .induced ..

namespace IsVacuum

variable {H} (x : W) (v w : Model H)

section

omit [μ.IsAddHaarMeasure]

@[simp] lemma add_apply : (v + w) x = v x + w x := rfl

@[simp] lemma smul_apply c : (c • v) x = c * v x := rfl

@[simp] lemma zero_apply : (0 : Model H) x = 0 := rfl

@[ext] lemma ext {v w : Model H} : (∀ x, v x = w x) → v = w := Subtype.ext ∘ funext

lemma norm_eq : ‖v‖ = ∫ x, ‖v x‖ ∂μ := L1.norm_of_fun_eq_integral_norm v.2.1

end

omit [μ.IsAddHaarMeasure] in
@[local simp] lemma norm_apply_le : ‖v x‖ ≤ ‖v‖ :=
  v.2.2 x ▸ by simp [norm_eq, v.2.1, he.norm_le_one]

section

omit [μ.IsAddHaarMeasure]

@[fun_prop] lemma continuous : Continuous v := v.2.elim (continuous_of_dominated (he.rec
  (by fun_prop)) (by simp [he.norm_le_one]) ·.norm (.of_forall (he.rec (by fun_prop))) |>.congr)

/-- The Heisenberg representation on the reproducing space of the vacuum e, in which y in W acts
by the L¹ isometry sending v to x ↦ β(y,x)v(x−y). -/
def heisRep : H.Rep (Model H) :=
  let ρ y : _ →ₗᵢ[ℂ] _ := by
    use! fun v ↦ ⟨fun x ↦ H.β y x * v (x - y), (v.2.1.comp_sub_right y).mono
      (by fun_prop) (by simp), fun x ↦ (integral_add_right_eq_self _ y).symm.trans (by
      simp [↓← v.2.2 (x - _), ← integral_const_mul, sub_eq_add_neg]; ac_nf)⟩
    iterate 2 solve_by_elim [ext, mul_add, mul_left_comm]
    simp [↓norm_eq, coe, integral_sub_right_eq_self fun _ ↦ ‖_‖]
  ⟨(ρ · |>.toContinuousLinearMap), by
    simp [↓he.ext_iff, ↓smul_apply, ρ, coe, sub_eq_add_neg]; grind,
    (ρ · |>.2), continuous_prod_of_continuous_lipschitzWith' _ _ (ρ · |>.lipschitz) fun v ↦
    have h (w : Model H) := w.2.1.norm
    .of_at fun a ↦ tendsto_iff_norm_sub_tendsto_zero.2 (by
      simpa [norm_map, integral_sub, h, ← norm_eq, neg_add_eq_sub] using ((continuous_of_dominated
      (fun t ↦ ((h (ρ t v)).sub (h (-ρ a v + ρ t v))).1) (by simp [(abs_norm_sub_norm_le ..).trans])
      (h (-ρ a v)) (.of_forall (by simp [↓add_apply, ρ, coe]; fun_prop))).tendsto a).const_sub ‖v‖)⟩

/-- For x in W, the Heisenberg operator on the reproducing space of the vacuum: it sends v to
the function z ↦ β(x,z) v(z−x). -/
abbrev heisOp : Model H →L[ℂ] Model H := heisRep.ρ x

/-- The function e itself, viewed as an element of the reproducing space it defines. -/
def vacElem : Model H := ⟨e, he.6, by simpa [he.2] using he.5 0⟩

def modelEval : Model H →L[ℂ] ℂ := mkContinuous (by use! (· x) <;> simp) 1 (by simp [coe])

/-- For σ an isometric ring endomorphism of ℂ and strongly continuous linear contractions K(y):
X → Y, the bounded σ-semilinear map v ↦ (x ↦ ∫ σ(v(y)) K(y)x dμ(y)) on the reproducing
space. -/
def kernelIntegral (σ : ℂ →+* ℂ) [RingHomIsometric σ] (K : W → X →L[ℂ] Y) (hK : ∀ x,
  Continuous (K · x)) (hC : ∀ y x, ‖K y x‖ ≤ ‖x‖) : Model H →SL[σ] X →L[ℂ] Y :=
  have hi (v : Model H) x := (v.2.1.smul_const x).mono ((σ.isometry.continuous.comp'
    (continuous v)).fun_smul (hK x)).aestronglyMeasurable (by simp_all)
  mkContinuous₂ (by apply mk₂'ₛₗ _ _ fun v x ↦ ∫ y, σ (v y) • K y x ∂μ <;>
    simp_all [add_smul, ← integral_smul, mul_comm]) 1
    (id fun v ↦ by simp_all [norm_eq, ← integral_mul_const, v.2.1.norm.mul_const])

/-- The bounded sesquilinear form on the reproducing space sending (v, w) to ∫ conj(v) w dμ,
conjugate-linear in the first argument. -/
def modelInner : Model H →L⋆[ℂ] Model H →L[ℂ] ℂ :=
  kernelIntegral _ modelEval continuous norm_apply_le

@[simp] lemma valueAt_apply : modelEval x v = v x := rfl

@[simp] lemma vacElem_apply : he.vacElem x = e x := rfl

end

@[simp] lemma heisOp_apply y : heisOp y v x = H.β y x * v (x - y) := rfl

attribute [irreducible] heisRep

omit [μ.IsAddHaarMeasure] in
lemma integrable_norm_sq : Integrable (‖v ·‖ ^ 2) μ :=
  (v.2.1.smul ‖v‖).mono (by fun_prop) (by simp [sq])

omit [μ.IsAddHaarMeasure] in
@[local simp] lemma modelInner_apply : modelInner v w = ∫ x, conj (v x) * w x ∂μ := rfl

omit [μ.IsAddHaarMeasure] in
lemma conj_modelInner : conj (modelInner v w) =
  modelInner w v := by simp [← integral_conj, mul_comm]

lemma modelInner_heisOp : modelInner (heisOp x v) (heisOp x w) = modelInner v w := by
  simp [mul_mul_mul_comm, ← integral_sub_right_eq_self (_ * w ·) x]

/-- Reproducing property: for v in the reproducing space of a vacuum e and x in W, the inner
product ⟨ρ(x)vac, v⟩ equals v(x). -/
@[simp] lemma modelInner_heisOp_vacElem : modelInner (heisOp x vacElem) v = v x :=
  v.2.2 x ▸ by simp [he.4, ← he.3 (_ - x), mul_comm]

omit [μ.IsAddHaarMeasure] in
lemma modelInner_self : modelInner v v = ∫ x, ‖v x‖ ^ 2 ∂μ := by simp [RCLike.conj_mul]; norm_cast

omit [μ.IsAddHaarMeasure] in
lemma eq_zero_of_modelInner_self {v} (h : he.modelInner v v = 0) : v = 0 :=
  norm_eq_zero.1 (by simp_all [↓modelInner_self, norm_eq, integral_eq_zero_iff_of_nonneg, Pi.le_def,
  integrable_norm_sq, v.2.1, Filter.EventuallyEq])

end IsVacuum

instance : CompleteSpace he.Model := NormedAddCommGroup.completeSpace_of_summable_imp_tendsto fun u
  h ↦ have hv := (Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.2 h)).trans ((ae_all_iff.2
    (u · |>.2.1.coeFn_toL1)).mono fun _ ↦ tsum_congr)
  have hi := .congr (by fun_prop) hv; ⟨⟨_, hi, by simp (maxDischargeDepth := 4) [← tsum_mul_right,
    (u _).2.symm, ← integral_tsum_of_summable_integral_norm, he.integrable_mul_kernel,
    h.of_norm_bounded,
    he.norm_eq, -Real.norm_eq_abs, he.norm_le_one]⟩, ((Topology.IsInducing.hasSum_iff ⟨rfl⟩
    ..).1 (Lp.ext (hv.trans hi.coeFn_toL1.symm) ▸ (Summable.of_norm ‹_›).hasSum)).tendsto_sum_nat⟩

variable {H} [CompleteSpace X] (R : H.Rep X) (T : X →L[ℂ] Y) (x : W)
  (v : Heisenberg.IsVacuum.Model H) (w : Heisenberg.IsVacuum.Model H) (f : X) [CompleteSpace Y]

/-- For a Heisenberg representation R on a Banach space X, the bounded bilinear map (v, f) ↦ ∫
v(y) R(y)f dμ(y), v in the reproducing space, f in X. -/
def Rep.integrated := he.kernelIntegral (.id _) R.ρ (by fun_prop) (by simp)

omit [μ.IsAddHaarMeasure] [CompleteSpace X] in
lemma Rep.integrated_apply : R.integrated v f = ∫ y, v y • R.ρ y f ∂μ := rfl

omit [μ.IsAddHaarMeasure] in
lemma Rep.map_integrated_eq_integral : T (R.integrated v f) = ∫ y, v y • T (R.ρ y f) ∂μ := by
  erw [← T.integral_comp_comm (v.2.1.smul_bdd ‖f‖ (by fun_prop) _)] <;> simp

@[simp] lemma Rep.integrated_heisOp : R.integrated (he.heisOp x v) f = R.ρ x (R.integrated v f) :=
  (integral_add_left_eq_self _ x).symm.trans (by simp [map_integrated_eq_integral, mul_comm])

omit [μ.IsAddHaarMeasure] in
lemma Rep.map_integrated {R' : H.Rep Y} (hT : ∀ y f, T (R.ρ y f) = R'.ρ y (T f)) : T (R.integrated v
  f) = R'.integrated v (T f) := by grind [map_integrated_eq_integral, integrated_apply]

namespace IsVacuum

omit [μ.IsAddHaarMeasure] in
lemma integrated_apply_eq_integral (R : H.Rep (Model H)) : R.integrated v w x = ∫ y,
  v y * R.ρ y w x ∂μ := R.map_integrated_eq_integral (modelEval x) ..

lemma integrated_vacElem : he.heisRep.integrated v vacElem = v :=
  ext (by simp [integrated_apply_eq_integral, v.2.2])

/-- For a bounded linear map T from the reproducing space to a complex Banach space and any v in
that space, Tv = ∫ v(y) T(ρ(y)vac) dμ(y). -/
lemma map_eq_integral (T : Model H →L[ℂ] Y) : T v = ∫ y, v y •
  T (heisOp y vacElem) ∂μ := by rw [← Rep.map_integrated_eq_integral, integrated_vacElem]

/-- Two bounded linear maps from the reproducing space to a complex Banach space that agree on
all translates ρ(y)vac, y in W, are equal. -/
lemma hom_ext {L L' : Model H →L[ℂ] Y} (h : ∀ y, L (heisOp y vacElem) = L' (heisOp y vacElem)) : L =
  L' := by grind +extAll [map_eq_integral]

/-- For v, w in the reproducing space of a vacuum e, with its Heisenberg representation ϱ, one
has v ⊗ w = ∫ v(y) ϱ(y)w dμ(y) = w(0)·v. -/
@[simp] lemma integrated_eq_smul : he.heisRep.integrated v w =
  w 0 • v := congr($(hom_ext (L' := .smulRightL ℂ _ _ (modelEval 0)) fun _ ↦ hom_ext fun _ ↦
  ext (by simp [integrated_apply_eq_integral, he.3, he.5, -add_left, field])) v w)

/-- A bounded continuous K: W → X, X Banach, yields a bounded linear L from the reproducing
space to X with M∘L = N whenever bounded linear M, N into the Banach space Y satisfy M(K(y))
= N(ρ(y)vac) for all y. -/
lemma exists_lift {K} (hK : Continuous K) {C} (hC : ∀ y, ‖K y‖ ≤ C) :
    ∃ L : Model H →L[ℂ] X, ∀ M N : _ →L[ℂ] Y, (∀ y, M (K y) = N (heisOp y vacElem)) → ∀ v, M (L v) =
  N v := have i (v : Model H) := v.2.1.smul_bdd _ (by fun_prop) (.of_forall hC)
  ⟨strongIntegral μ fun y ↦ (modelEval y).smulRight (K y), fun M _ _ _ ↦ by
    rw [strongIntegral_apply, ← M.integral_comp_comm, map_eq_integral] <;> aesop⟩

/-- Uniqueness of the invariant form: if B_z are bounded sesquilinear forms on the reproducing
space, z ↦ B_z(v,w) is integrable and ∫B_z dν is invariant under all ρ(x), then ∫B_z(v,w) dν
= (∫B_z(vac,vac) dν)·⟨v,w⟩. -/
lemma integral_form_eq_mul_modelInner [LocallyCompactSpace W] {Z m} {ν : @Measure Z m} (B : Z →
  Model H →L⋆[ℂ] _ →L[ℂ] ℂ) (hi : ∀ v w, Integrable (B · v w) ν) (hB : ∀ x f g, ∫ z,
  B z (heisOp x f) (heisOp x g) ∂ν = ∫ z, B z f g ∂ν) v w : ∫ z, B z v w ∂ν = (∫ z,
  B z vacElem vacElem ∂ν) * modelInner v w := have k v := strongIntegral_apply _ _ (hi v)
  have h x f := by simpa using hB x (heisOp (-x) f)
  have t u := strongIntegral_apply _ (fun z ↦
    innerSLFlip ℂ 1 ∘SL (B z).flip u) (hi · _ |>.inner_const _)
  k .. ▸ congr($(hom_ext (L' := (_ : ℂ) • _) fun y ↦ star_injective (by
    rw [k, h, ← k, map_eq_integral, ← integral_neg_eq_self]
    simpa [*, he.3, he.4, conj_modelInner, mul_comm, ← integral_conj] using
      (heisRep.map_integrated_eq_integral _ vacElem (heisOp (-y) v)).symm.trans (t ..))) w)
