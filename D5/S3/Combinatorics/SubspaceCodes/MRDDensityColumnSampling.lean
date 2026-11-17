/- GID: D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubspaceCodes/MRDDensityColumnSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-field MRD density: sampling argument. -/
/-
admission_basis: escape-witness
escape_witness: D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting.noninjective_map_count
question_answered: https://github.com/the-omega-institute/trureturing/issues/26598
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27411
Direct frozen declaration identities (not module pins):
none
Per-declaration proof_shape; escape_witness; consumers:
MRDDensityModel.imageCode: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityModel.imageFiberEquiv
MRDDensityModel.imageFiberEquiv: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityModel.imageEventEquiv, MRDDensityModel.injection_count_via_images
MRDDensityModel.imageEventEquiv: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityModel.image_event_card
MRDDensityModel.image_event_card: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityModel.uniform_image_ratio
MRDDensityModel.injection_count_via_images: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityModel.subspace_card_real, MRDDensityModel.uniform_image_ratio
MRDDensityModel.uniform_image_ratio: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.density_generator_ratio
MRDDensityCounting.injectionFrameEquiv: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityCounting.injection_count
MRDDensityCounting.injection_count: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityModel.real_injection_count
MRDDensityModel.real_injection_count: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityMoments.frame_card_gaussian, MRDDensityModel.subspace_card_real
MRDDensityModel.subspace_card_real: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.result
MRDDensityCounting.annihilating_map_count: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityCounting.annihilating_map_fraction, MRDDensityCounting.vanishing_map_count
MRDDensityCounting.annihilating_map_fraction: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnTensor.MRDDensityTensor.tensor_event_fraction
MRDDensityCounting.vanishing_map_count: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityCounting.noninjective_map_count
MRDDensityCounting.noninjective_map_count: proof_shape=content; escape_witness=MRDDensityCounting.noninjective_map_count; consumers=MRDDensityCounting.noninjective_map_fraction
MRDDensityCounting.noninjective_map_fraction: proof_shape=content; escape_witness=MRDDensityCounting.noninjective_map_count; consumers=MRDDensityCounting.fixed_source_injection_limit, MRDDensityCounting.noninjective_fraction_limit
MRDDensityCounting.injective_fraction_eq_one_sub: proof_shape=bind-only; escape_witness=none; consumers=MRDDensityCounting.fixed_source_injection_limit, MRDDensityCounting.injective_fraction_limit
MRDDensityCounting.noninjective_fraction_limit: proof_shape=content; escape_witness=MRDDensityCounting.noninjective_map_count; consumers=MRDDensityCounting.injective_fraction_limit
MRDDensityCounting.injective_fraction_limit: proof_shape=content; escape_witness=MRDDensityCounting.noninjective_map_count; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.result
MRDDensityCounting.fixed_source_injection_limit: proof_shape=bind-only; escape_witness=none; consumers=D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityScalar.normalized_gaussian_limit, D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnLimit.MRDDensityTuples.weighted_frame_moment_limit
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Analysis.SpecificLimits.Normed

open Module
open scoped BigOperators
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityModel
variable {K D E : Type*} [Field K]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

noncomputable def imageCode (f : {f : D →ₗ[K] E // Function.Injective f}) :
    {U : Submodule K E // finrank K U = finrank K D} :=
  ⟨LinearMap.range f.val, LinearMap.finrank_range_of_inj f.property⟩

private noncomputable def imageFiberEquiv (U : {U : Submodule K E // finrank K U = finrank K D}) :
    {f : {f : D →ₗ[K] E // Function.Injective f} // imageCode f = U} ≃ (D ≃ₗ[K] D) := by
  classical
  let e0 : D ≃ₗ[K] U.val := LinearEquiv.ofFinrankEq D U.val U.property.symm
  let toAut := fun f : {f : {f : D →ₗ[K] E // Function.Injective f} // imageCode f = U} =>
    ((LinearEquiv.ofInjective f.val.val f.val.property).trans
      (LinearEquiv.ofEq _ _ (congrArg Subtype.val f.property))).trans e0.symm
  have hrange (e : D ≃ₗ[K] D) :
      LinearMap.range (U.val.subtype.comp (e.trans e0).toLinearMap) = U.val := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  refine
    { toFun := toAut
      invFun := fun e => ⟨⟨U.val.subtype.comp (e.trans e0).toLinearMap,
        U.val.subtype_injective.comp (e.trans e0).injective⟩, Subtype.ext (hrange e)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply Subtype.ext
    apply Subtype.ext
    ext x
    change (e0 (toAut f x) : E) = f.val.val x
    simp [toAut, LinearEquiv.trans_apply]
    rfl
  · intro e
    ext x
    change e0.symm _ = e x
    apply e0.symm_apply_eq.mpr
    apply Subtype.val_injective
    rfl

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityModel
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityModel
variable {K D E : Type*} [Field K]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

private noncomputable def imageEventEquiv
    (P : {U : Submodule K E // finrank K U = finrank K D} → Prop) :
    {f : {f : D →ₗ[K] E // Function.Injective f} // P (imageCode f)} ≃
      {U : {U : Submodule K E // finrank K U = finrank K D} // P U} × (D ≃ₗ[K] D) :=
  (Equiv.sigmaSubtypeFiberEquivSubtype imageCode (fun _ => Iff.rfl)).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (fun U => imageFiberEquiv U.val))

private theorem image_event_card [Finite K] [Finite D] [Finite E]
    (P : {U : Submodule K E // finrank K U = finrank K D} → Prop) :
    Nat.card {f : {f : D →ₗ[K] E // Function.Injective f} // P (imageCode f)} =
      Nat.card {U : {U : Submodule K E // finrank K U = finrank K D} // P U} *
        Nat.card (D ≃ₗ[K] D) := by
  rw [Nat.card_congr (imageEventEquiv P), Nat.card_prod]

private theorem injection_count_via_images [Finite K] [Finite D] [Finite E] :
    Nat.card {f : D →ₗ[K] E // Function.Injective f} =
      Nat.card {U : Submodule K E // finrank K U = finrank K D} * Nat.card (D ≃ₗ[K] D) := by
  let e := (Equiv.sigmaFiberEquiv (imageCode (K := K) (D := D) (E := E))).symm.trans
    (Equiv.sigmaEquivProdOfEquiv (imageFiberEquiv (K := K) (D := D) (E := E)))
  rw [Nat.card_congr e, Nat.card_prod]

theorem uniform_image_ratio [Finite K] [Finite D] [Finite E]
    (P : {U : Submodule K E // finrank K U = finrank K D} → Prop) :
    (Nat.card {f : {f : D →ₗ[K] E // Function.Injective f} // P (imageCode f)} : ℝ) /
        (Nat.card {f : D →ₗ[K] E // Function.Injective f} : ℝ) =
      (Nat.card {U : {U : Submodule K E // finrank K U = finrank K D} // P U} : ℝ) /
        (Nat.card {U : Submodule K E // finrank K U = finrank K D} : ℝ) := by
  letI : Finite (D ≃ₗ[K] D) := Finite.of_injective
    (fun e : D ≃ₗ[K] D => (e : D → D)) DFunLike.coe_injective
  have ha : (Nat.card (D ≃ₗ[K] D) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := D ≃ₗ[K] D)).ne'
  rw [image_event_card, injection_count_via_images, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_right _ _ ha]

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityModel
open Module
open scoped BigOperators
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting
variable {K E : Type*} [Field K] [Fintype K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

noncomputable def injectionFrameEquiv (k : ℕ) :
    {f : (Fin k → K) →ₗ[K] E // Function.Injective f} ≃
      {v : Fin k → E // LinearIndependent K v} := by
  let b := Pi.basisFun K (Fin k)
  apply Equiv.subtypeEquiv (b.constr K).symm.toEquiv
  intro f
  change Function.Injective f ↔ LinearIndependent K (fun i => f (b i))
  constructor
  · intro hf
    exact b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  · intro hv
    apply LinearMap.ker_eq_bot.mp
    have h := Submodule.range_ker_disjoint hv
    simpa only [b.span_eq, top_inf_eq] using h.eq_bot

private theorem injection_count (k : ℕ) (hk : k ≤ finrank K E) :
    Nat.card {f : (Fin k → K) →ₗ[K] E // Function.Injective f} =
      ∏ i : Fin k, (Fintype.card K ^ finrank K E - Fintype.card K ^ i.val) := by
  letI : Finite E := Nat.finite_of_card_ne_zero (by
    rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]
    exact pow_ne_zero _ Fintype.card_ne_zero)
  rw [Nat.card_congr (injectionFrameEquiv k)]
  exact card_linearIndependent hk

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityModel
open D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting
variable {K E : Type*} [Field K] [Fintype K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem real_injection_count (k : ℕ) (hk : k ≤ finrank K E) :
    (Nat.card {f : (Fin k → K) →ₗ[K] E // Function.Injective f} : ℝ) =
      ∏ h ∈ Finset.range k, ((Fintype.card K : ℝ)^finrank K E - (Fintype.card K : ℝ)^h) := by
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  have hsub (i : Fin k) : Fintype.card K ^ i.val ≤ Fintype.card K ^ finrank K E :=
    Nat.pow_le_pow_right hq (le_trans (Nat.le_of_lt i.isLt) hk)
  rw [injection_count k hk, Nat.cast_prod]
  simp_rw [Nat.cast_sub (hsub _), Nat.cast_pow]
  exact Fin.prod_univ_eq_prod_range (fun h => ((Fintype.card K : ℝ)^finrank K E - (Fintype.card K : ℝ)^h)) k

theorem subspace_card_real (k : ℕ) (hk : k ≤ finrank K E) :
    (Nat.card {U : Submodule K E // finrank K U = k} : ℝ) =
      ∏ h ∈ Finset.range k,
        ((Fintype.card K : ℝ)^finrank K E - (Fintype.card K : ℝ)^h) /
          ((Fintype.card K : ℝ)^k - (Fintype.card K : ℝ)^h) := by
  classical
  let D := Fin k → K
  letI : Finite E := Nat.finite_of_card_ne_zero (by
    rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]
    exact pow_ne_zero _ Fintype.card_ne_zero)
  letI : Finite (D ≃ₗ[K] D) := Finite.of_injective
    (fun e : D ≃ₗ[K] D => (e : D → D)) DFunLike.coe_injective
  let e : {f : D →ₗ[K] D // Function.Injective f} ≃ (D ≃ₗ[K] D) :=
    { toFun := fun f => LinearEquiv.ofInjectiveEndo f.val f.property
      invFun := fun f => ⟨f.toLinearMap, f.injective⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => by ext; rfl }
  have hauto : (Nat.card (D ≃ₗ[K] D) : ℝ) =
      ∏ h ∈ Finset.range k, ((Fintype.card K : ℝ)^k - (Fintype.card K : ℝ)^h) := by
    rw [← Nat.card_congr e]
    simpa only [D, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      (real_injection_count (K := K) (E := D) k (by simp [D]))
  have ha : (Nat.card (D ≃ₗ[K] D) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := D ≃ₗ[K] D)).ne'
  have hc := injection_count_via_images (K := K) (D := D) (E := E)
  have hcR := congrArg (fun z : ℕ => (z : ℝ)) hc
  simp only [Nat.cast_mul, D, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hcR
  have hcount := real_injection_count (K := K) (E := E) k hk
  change (Nat.card {f : D →ₗ[K] E // Function.Injective f} : ℝ) = _ at hcount
  rw [hcount] at hcR
  rw [Finset.prod_div_distrib, ← hauto, eq_div_iff ha]
  exact hcR.symm

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityModel
open Module
open scoped BigOperators
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting
variable {K E F : Type*} [Field K] [Fintype K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

private theorem annihilating_map_count (T : Submodule K E) :
    Nat.card {f : E →ₗ[K] F // T ≤ LinearMap.ker f} =
      Fintype.card K ^ ((finrank K E - finrank K T) * finrank K F) := by
  let e : {f : E →ₗ[K] F // LinearMap.ker T.mkQ ≤ LinearMap.ker f} ≃
      ((E ⧸ T) →ₗ[K] F) := T.mkQ.liftOfSurjective T.mkQ_surjective
  have hc : Nat.card {f : E →ₗ[K] F // T ≤ LinearMap.ker f} =
      Nat.card ((E ⧸ T) →ₗ[K] F) := by
    simpa only [Submodule.ker_mkQ] using Nat.card_congr e
  rw [hc, Module.natCard_eq_pow_finrank (K := K),
    Module.finrank_linearMap (R := K) (S := K),
    Submodule.finrank_quotient, Nat.card_eq_fintype_card]

theorem annihilating_map_fraction (T : Submodule K E) :
    (Nat.card {f : E →ₗ[K] F // T ≤ LinearMap.ker f} : ℝ) /
      (Nat.card (E →ₗ[K] F) : ℝ) =
      ((Fintype.card K : ℝ) ^ (finrank K T * finrank K F))⁻¹ := by
  have hq : Fintype.card K ≠ 0 := Fintype.card_ne_zero
  have hqR : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hexp : (finrank K E - finrank K T) * finrank K F +
      finrank K T * finrank K F = finrank K E * finrank K F := by
    rw [← Nat.add_mul, Nat.sub_add_cancel T.finrank_le]
  rw [annihilating_map_count, Module.natCard_eq_pow_finrank (K := K), Module.finrank_linearMap (R := K) (S := K),
    Nat.card_eq_fintype_card, Nat.cast_pow, Nat.cast_pow, ← hexp, pow_add]
  exact div_mul_cancel_left₀ (pow_ne_zero _ hqR) _

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting
variable {K D E : Type*} [Field K] [Fintype K]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

private theorem vanishing_map_count (x : D) (hx : x ≠ 0) :
    Nat.card {f : D →ₗ[K] E // f x = 0} =
      Fintype.card K ^ ((finrank K D - 1) * finrank K E) := by
  have he : {f : D →ₗ[K] E // f x = 0} ≃
      {f : D →ₗ[K] E // K ∙ x ≤ LinearMap.ker f} :=
    Equiv.subtypeEquivRight (fun f => by simp [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker])
  rw [Nat.card_congr he, annihilating_map_count, finrank_span_singleton hx]

private theorem noninjective_map_count :
    Nat.card {f : D →ₗ[K] E // ¬ Function.Injective f} ≤
      Fintype.card K ^ finrank K D *
        Fintype.card K ^ ((finrank K D - 1) * finrank K E) := by
  classical
  letI : Finite D := Nat.finite_of_card_ne_zero (by
    rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]
    exact pow_ne_zero _ Fintype.card_ne_zero)
  letI : Finite E := Nat.finite_of_card_ne_zero (by
    rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card]
    exact pow_ne_zero _ Fintype.card_ne_zero)
  letI : Fintype D := Fintype.ofFinite D
  letI : Finite (D →ₗ[K] E) := Finite.of_injective
    (fun f : D →ₗ[K] E => (f : D → E)) DFunLike.coe_injective
  have hx (f : {f : D →ₗ[K] E // ¬ Function.Injective f}) :
      ∃ x : D, x ≠ 0 ∧ f.val x = 0 := by
    by_contra! hn
    apply f.property
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hfx
    by_contra hx
    exact hn x hx hfx
  let e : {f : D →ₗ[K] E // ¬ Function.Injective f} →
      Σ x : {x : D // x ≠ 0}, {f : D →ₗ[K] E // f x.val = 0} := fun f =>
    ⟨⟨(hx f).choose, (hx f).choose_spec.1⟩, ⟨f.val, (hx f).choose_spec.2⟩⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : Σ x : {x : D // x ≠ 0}, {f : D →ₗ[K] E // f x.val = 0} => z.2.val) hab
  have hc := Nat.card_le_card_of_injective e he
  rw [Nat.card_sigma] at hc
  have hcount (x : {x : D // x ≠ 0}) : Nat.card {f : D →ₗ[K] E // f x.val = 0} =
      Fintype.card K ^ ((finrank K D-1)*finrank K E) := vanishing_map_count x.val x.property
  simp_rw [hcount] at hc
  simp only [Finset.sum_const, nsmul_eq_mul] at hc
  apply hc.trans
  apply Nat.mul_le_mul_right
  calc
    Fintype.card {x : D // x ≠ 0} ≤ Fintype.card D := Fintype.card_subtype_le _
    _ = Fintype.card K ^ finrank K D := Module.card_eq_pow_finrank (K := K)

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting
open Filter Topology
open scoped Topology
variable {K D E : Type*} [Field K] [Fintype K]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

private theorem noninjective_map_fraction (hD : 1 ≤ finrank K D) :
    (Nat.card {f : D →ₗ[K] E // ¬ Function.Injective f} : ℝ) /
      (Nat.card (D →ₗ[K] E) : ℝ) ≤
      (Fintype.card K : ℝ)^finrank K D / (Fintype.card K : ℝ)^finrank K E := by
  have hq0 : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hc := noninjective_map_count (K := K) (D := D) (E := E)
  have hcR : (Nat.card {f : D →ₗ[K] E // ¬ Function.Injective f} : ℝ) ≤
      (Fintype.card K : ℝ)^finrank K D *
        (Fintype.card K : ℝ)^((finrank K D-1)*finrank K E) := by exact_mod_cast hc
  rw [Module.natCard_eq_pow_finrank (K := K) (V := D →ₗ[K] E), Module.finrank_linearMap (R := K) (S := K),
    Nat.card_eq_fintype_card (α := K), Nat.cast_pow]
  apply (div_le_div_of_nonneg_right hcR (pow_nonneg hq0.le _)).trans_eq
  have hexp : finrank K D * finrank K E = (finrank K D-1)*finrank K E + finrank K E := by
    calc
      _ = (finrank K D-1+1)*finrank K E := by rw [Nat.sub_add_cancel hD]
      _ = _ := by ring
  rw [hexp, pow_add]
  field_simp [ne_of_gt hq0]

private theorem injective_fraction_eq_one_sub [Finite D] [Finite E] :
    (Nat.card {f : D →ₗ[K] E // Function.Injective f} : ℝ) / (Nat.card (D →ₗ[K] E) : ℝ) =
      1 - (Nat.card {f : D →ₗ[K] E // ¬ Function.Injective f} : ℝ) /
        (Nat.card (D →ₗ[K] E) : ℝ) := by
  classical
  letI : Finite (D →ₗ[K] E) := Finite.of_injective
    (fun f : D →ₗ[K] E => (f : D → E)) DFunLike.coe_injective
  letI : Fintype (D →ₗ[K] E) := Fintype.ofFinite _
  have hc : Nat.card {f : D →ₗ[K] E // ¬ Function.Injective f} =
      Nat.card (D →ₗ[K] E) - Nat.card {f : D →ₗ[K] E // Function.Injective f} := by
    simp only [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl _
  have hsub : Nat.card {f : D →ₗ[K] E // Function.Injective f} ≤ Nat.card (D →ₗ[K] E) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hden : (Nat.card (D →ₗ[K] E) : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := D →ₗ[K] E)).ne'
  rw [hc, Nat.cast_sub hsub, sub_div, div_self hden]
  ring

private theorem noninjective_fraction_limit (r n : ℕ) (hr : 1 ≤ r) (hrn : r < n) :
    Tendsto (fun m : ℕ =>
      (Nat.card {f : (Fin (m*r) → K) →ₗ[K] (Fin (m*n) → K) // ¬ Function.Injective f} : ℝ) /
        (Nat.card ((Fin (m*r) → K) →ₗ[K] (Fin (m*n) → K)) : ℝ)) atTop (𝓝 0) := by
  have hq : (1 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hq0 : (0 : ℝ) < Fintype.card K := lt_trans zero_lt_one hq
  have hgeo : Tendsto (fun m : ℕ => ((Fintype.card K : ℝ)^m)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_nonneg.mpr hq0.le) (inv_lt_one_of_one_lt₀ hq)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgeo
  · exact Filter.Eventually.of_forall (fun m => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmD : 1 ≤ Module.finrank K (Fin (m*r) → K) := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      exact Nat.mul_pos hm hr
    have hc := noninjective_map_fraction (K := K) (D := Fin (m*r) → K)
      (E := Fin (m*n) → K) hmD
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hc
    apply hc.trans
    rw [inv_eq_one_div, div_le_div_iff₀ (pow_pos hq0 _) (pow_pos hq0 _), one_mul, ← pow_add]
    apply pow_le_pow_right₀ hq.le
    have h := Nat.mul_le_mul_left m (Nat.succ_le_of_lt hrn)
    simpa only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] using h

theorem injective_fraction_limit (r n : ℕ) (hr : 1 ≤ r) (hrn : r < n) :
    Tendsto (fun m : ℕ =>
      (Nat.card {f : (Fin (m*r) → K) →ₗ[K] (Fin (m*n) → K) // Function.Injective f} : ℝ) /
        (Nat.card ((Fin (m*r) → K) →ₗ[K] (Fin (m*n) → K)) : ℝ)) atTop (𝓝 1) := by
  simpa only [injective_fraction_eq_one_sub, sub_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      (noninjective_fraction_limit (K := K) r n hr hrn)

end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting
namespace D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting
open Filter
open scoped Topology
variable {K : Type*} [Field K] [Fintype K]
theorem fixed_source_injection_limit (k r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun m : ℕ =>
      (Nat.card {f : (Fin k → K) →ₗ[K] (Fin (m*r) → K) // Function.Injective f} : ℝ) /
        (Nat.card ((Fin k → K) →ₗ[K] (Fin (m*r) → K)) : ℝ)) atTop (𝓝 1) := by
  by_cases hk : k=0
  · subst k
    have he (m : ℕ) :
        {f : (Fin 0 → K) →ₗ[K] (Fin (m*r) → K) // Function.Injective f} ≃
          ((Fin 0 → K) →ₗ[K] (Fin (m*r) → K)) :=
      Equiv.subtypeUnivEquiv (fun f => Function.injective_of_subsingleton f)
    have hc (m : ℕ) :
        (Nat.card {f : (Fin 0 → K) →ₗ[K] (Fin (m*r) → K) // Function.Injective f} : ℝ) /
          (Nat.card ((Fin 0 → K) →ₗ[K] (Fin (m*r) → K)) : ℝ) = 1 := by
      rw [Nat.card_congr (he m)]
      apply div_self
      exact_mod_cast (Nat.card_pos (α := (Fin 0 → K) →ₗ[K] (Fin (m*r) → K))).ne'
    simpa only [hc] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hq : (1 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hq0 : (0 : ℝ) < Fintype.card K := lt_trans zero_lt_one hq
  have hgeo : Tendsto (fun m : ℕ => (Fintype.card K : ℝ)^k*((Fintype.card K : ℝ)^m)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_nonneg.mpr hq0.le) (inv_lt_one_of_one_lt₀ hq)).const_mul ((Fintype.card K : ℝ)^k)
    simpa only [← inv_pow, mul_zero] using h
  have hzero : Tendsto (fun m : ℕ =>
      (Nat.card {f : (Fin k → K) →ₗ[K] (Fin (m*r) → K) // ¬ Function.Injective f} : ℝ) /
        (Nat.card ((Fin k → K) →ₗ[K] (Fin (m*r) → K)) : ℝ)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgeo
    · exact Eventually.of_forall (fun m => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    · apply Eventually.of_forall
      intro m
      have h := noninjective_map_fraction (K := K) (D := Fin k → K)
        (E := Fin (m*r) → K) (by simpa using Nat.one_le_iff_ne_zero.mpr hk)
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
      apply h.trans
      rw [← div_eq_mul_inv]
      apply div_le_div_of_nonneg_left (pow_nonneg hq0.le _) (pow_pos hq0 _)
      exact pow_le_pow_right₀ hq.le (by simpa using Nat.mul_le_mul_left m hr)
  simpa only [injective_fraction_eq_one_sub, sub_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hzero
end D5.S3.Combinatorics.SubspaceCodes.MRDDensityColumnSampling.MRDDensityCounting
