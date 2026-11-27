/- GID: D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/AlgebraicForms
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/CuspForms/AlgebraicForms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.CuspForms.AlgebraicForms. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/CuspForms/AlgebraicForms.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.HeckePolyEval
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.WeightParameter
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms
(known result; see Lib.Adelic.CuspForms.Petersson).

This file: Forms on a definite unitary group are algebraic modular forms; integrals become class
sums. -/
seal Finset.univ Finset.sum Finset.prod

attribute [-simp] Fintype.card_pi

variable {E n} [Field E] [CMType E] [Fintype n] {κ}
  {e : NumberField.InfinitePlace E → ℤ} {l s} {V : Space E n s} [i : V.IsStd] {φ : AlgForm n κ e}
  (h : IsHCParam (n := n) κ e l) (ψ : AlgForm n κ e)

lemma isStd_signedSpace [StablyUnram E] (hs : s = 1) : (signedSpace E s).IsStd := ⟨hs, by aesop⟩

namespace Space

lemma algFormCoeff_algFormRep L a g : algFormCoeff s L (algFormRep κ e a φ) g =
  algFormCoeff s L φ (g * (1, a)) := by aesop

open Subgroup

/-- Let V be standard, F automorphic, and K an open subgroup of K₀. Then ∫_{Γ\G} F equals
[K₀:K]⁻¹ times the integral over Γ\G_f, with vol K = 1, of g ↦ ∫_{G_∞} F(x, g) dx. -/
lemma integral_eq_classIntegral_of_isLevel {F} (hF : V.IsAutomorphic F) {K} (o : IsLevel K) : ∫ g,
  F g ∂V.quotMeasure = (stdLevelIndex K : ℂ)⁻¹ * classIntegral stdRatPoints K (∫ x, F ⟨x, ·⟩) := by
  have ⟨a, b, L, k⟩ := hF; induction i
  simp [inf_of_le_left, integral_quotMeasure_eq_classSum b (by tauto) _ (o :=
    ⟨inf_le_of_right_le o.1, (isOpen_mono (H₂ := rightStab _) (show ∀ _ ∈ L.1, ∀ _, _ from
      (by simp [← k · · ⟨_, ·⟩])) L.2).inter o.2⟩) inf_le_left a,
    classIntegral, ← relIndex_inf_mul_relIndex, Rat.smul_def, o.1, field]

attribute [local simp] dsKernel algFormCoeff_apply realConv typeKernel gramForm_highestVector_self
  mul_assoc schur_orthogonality

/-- Let V be standard and φ an algebraic form of weight (κ, e) with open stabiliser under right
translation. For every linear functional L, the function g ↦ L(ḡ_∞⁻¹ φ(g_f)) on G
(`algFormCoeff`) is automorphic. -/
lemma isAutomorphic_algFormCoeff {L} : V.IsAutomorphic (algFormCoeff s L ψ) := i.std_induction
    ⟨L.continuous_on_pi.comp (.matrix_mulVec (by simp [weylRep, -Pi.inv_apply]; fun_prop)
    (isLocallyConstant_of_eventually_mul (OpenSubgroup.mem_nhds_one ⟨rightStab ψ.1,
  ψ.2.1⟩)).continuous.snd'), by
    rintro _ ⟨γ, rfl⟩ g; erw [algFormCoeff_apply, ψ.2.2]; simp [weightRep], ⟨_, ψ.2.1⟩, fun _ ↦
  (by simp [· _])⟩

lemma star_ofAlgForm (h : s = 1) x g : star (ofAlgForm l s φ (x, g)) = gramForm (φ.1 g)
    (conjWeylRep κ e x (highestVector κ l)) := by cases h; simp [← gramForm_conjWeylRep (e :=
  e) x⁻¹ (φ.1 _), conj_gramForm]

include h

/-- On a standard space, for l = 2λ the parameter of (κ, e), φ a smooth algebraic form and Φ
automorphic with Φ(x, g) = L_g(ρ(x)v⁺), L_g linear: ∫_{[G]} ΦF_φ = (dim ρ)⁻¹ ∫_{Γ\G_f}
L_g(φ(g)) dg, with F_φ = `ofAlgForm` and vol K₀ = 1. -/
lemma integral_mul_eq_classIntegral K [IsLevel K] {Φ} (hΦ : V.IsAutomorphic Φ) (L : _ →
  _ →ₗ[ℂ] ℂ) (H : ∀ x g, Φ (x, g) = L g (conjWeylRep κ e x (highestVector κ l))) : ∫ g,
  Φ g * ofAlgForm l s φ g ∂V.quotMeasure = (Fintype.card (WeylIndex n κ) * stdLevelIndex K :
  ℂ)⁻¹ * classIntegral stdRatPoints K fun g ↦ L g (φ.1 g) := by cases i.1; simp [H, h _,
  ↓integral_eq_classIntegral_of_isLevel (hΦ.map₂ (isAutomorphic_algFormCoeff φ) (· * ·)) ‹_›]

lemma isForm_ofAlgForm : V.IsForm (typeKernel l s) (ofAlgForm l s ψ) :=
  i.std_induction ⟨isAutomorphic_algFormCoeff ψ, ((stdSpace ..).isAutomorphic_algFormCoeff
  ψ).mem_rapidFunctions.2.bounded, by simp [funext_iff, h.prod_formalDegree, h _,
  ← h.gramForm_conjWeylRep_eq_dsCoeff, ← Complex.ofReal_prod]⟩

/-- For V standard and l twice the Harish-Chandra parameter of (κ, e), the linear isomorphism F
↦ φ_F from forms of type e_l to smooth algebraic forms of weight (κ, e). -/
noncomputable def toAlgForm (V : Space E n s) [i : V.IsStd] (h : IsHCParam κ e l) :
  V.Form (typeKernel l s) ≃ₗ[ℂ] AlgForm n κ e := .symm (.ofBijective ((ofAlgForm ..).codRestrict _
  (isForm_ofAlgForm h)) (by exact i.std_induction ⟨(injective_iff_map_eq_zero _).2 fun φ z ↦ by
  ext; exact highestVector_cyclic (h · |>.1) e (.proj _) _ (.inl (inv_inv · ▸ congr($z.1 (_, _)))),
  fun ⟨y, ⟨c, r, K, k⟩, _, f⟩ ↦
  ⟨⟨fun g ↦ ∫ x, (Fintype.card (WeylIndex n κ) * y (x, g)) • conjWeylRep κ e x (highestVector κ l),
  isOpen_mono (H₁ := K.1) (H₂ := rightStab _) (fun a b g ↦ by simp [← k a b ⟨_, g⟩]) K.2,
  fun γ g ↦ ((MeasureTheory.integral_mul_left_eq_self
  ..).symm.trans (by simp [← r _ ⟨γ, rfl⟩ (_, g)]; rfl)).trans ((weightRep κ e _
  γ).toContinuousLinearMap.integral_comp_comm integrable_of_compactSpace)⟩, Subtype.ext (.trans
  (funext fun ⟨x, g⟩ ↦ ((MeasureTheory.integral_mul_left_eq_self _ x).trans ((gramForm (n :=
  n) _ ∘ₗ conjWeylRep κ e _).toContinuousLinearMap.integral_comp_comm
  integrable_of_compactSpace)).symm.trans (by
    simp [h.prod_formalDegree, h.gramForm_conjWeylRep_eq_dsCoeff, ← Complex.ofReal_prod]; ac_rfl))
  (f integrable_of_compactSpace))⟩⟩))

lemma ofAlgForm_toAlgForm y : ofAlgForm l s (V.toAlgForm h y) = y := congr($((V.toAlgForm h).3 y))

/-- The isomorphism `Space.toAlgForm` from forms of type e_l to smooth algebraic forms of weight
(κ, e) commutes with right translation by G_f. -/
@[local simp] lemma toAlgForm_formRep a y : V.toAlgForm h (V.formRep _ a y) =
  algFormRep κ e a (V.toAlgForm h y) := (V.toAlgForm h).eq_symm_apply.1 (Subtype.ext
  ((funext (algFormCoeff_algFormRep _ _)).trans congr($(ofAlgForm_toAlgForm h y) ∘ _)).symm)

variable (V)

/-- For V standard, l twice the Harish-Chandra parameter of (κ, e) and K a subgroup of G_f, the
isomorphism φ ↦ F_φ from K-fixed algebraic forms to K-fixed forms of type e_l. -/
noncomputable def algFormEquiv K : levelSpace (algFormRep κ e) K ≃ₗ[ℂ] levelSpace (V.formRep
  (typeKernel l s)) K := (V.toAlgForm h).symm.ofSubmodules _ _ (by ext; simp [↓← toAlgForm_formRep])

/-- For V standard and l twice the Harish-Chandra parameter of (κ, e), a form y of type e_l is
spherical at w with Hecke polynomial p if and only if its algebraic form, as a function on
G_f, is. -/
lemma _root_.isSphericalWith_toAlgForm_iff [WeilData E] {y w p} {u : _ ≠ w} : IsSphericalWith
  (rightRegular ..) u p (V.toAlgForm h y).1 ↔ IsSphericalWith (V.formRep _) u p y := by
  simp [IsSphericalWith, ← (V.toAlgForm h).apply_eq_iff_eq, Subtype.ext_iff]; congr!
  exact (map_heckePolyOp ((AlgForm ..).subtype ∘ₗ (V.toAlgForm h).1) _ (by simp)).symm
