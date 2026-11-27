/- GID: D5/S3/FiniteGroups/Cyclic/RealIrreducibleDegreeBound
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/RealIrreducibleDegreeBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A real irreducible degree bound and the P48p small-order application. -/

import D5.S3.FiniteGroups.FiniteCharacterAlgebra
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.TensorProduct.Tower
import OmegaBuild.Commands

/-!
The real-part image of a nonzero complex constituent of a real representation
is a nonzero real subrepresentation. In real irreducible degree this makes the
real part surjective, and the complex density theorem bounds the constituent.
-/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

open scoped TensorProduct MonoidAlgebra

namespace ExtremalC48

open D5.S3.FiniteGroups.FiniteCharacterAlgebra
open D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation
  (asAlgebraHom_surjective_of_isIrreducible)

variable {H V : Type*} [AddCommGroup V] [Module ℝ V]

private def complexification [Monoid H] (ρ : Representation ℝ H V) :
    Representation ℂ H (ℂ ⊗[ℝ] V) :=
  (Module.End.baseChangeHom ℝ ℂ V).toMonoidHom.comp ρ

private def realPart : ℂ ⊗[ℝ] V →ₗ[ℝ] V :=
  (TensorProduct.lid ℝ V).toLinearMap.comp (Complex.reLm.rTensor V)

private theorem realPart_tmul (c : ℂ) (v : V) :
    realPart (c ⊗ₜ[ℝ] v) = c.re • v :=
  rfl

private theorem realPart_equivariant [Monoid H] (ρ : Representation ℝ H V) (g : H)
    (z : ℂ ⊗[ℝ] V) : realPart (complexification ρ g z) = ρ g (realPart z) := by
  have heq :
      realPart.comp ((complexification ρ g).restrictScalars ℝ) = (ρ g).comp realPart := by
    apply TensorProduct.ext'
    intro c v
    change realPart (c ⊗ₜ[ℝ] ρ g v) = ρ g (realPart (c ⊗ₜ[ℝ] v))
    rw [realPart_tmul, realPart_tmul, map_smul]
  exact LinearMap.congr_fun heq z

private theorem eq_zero_of_realPart_of_I (z : ℂ ⊗[ℝ] V)
    (hre : realPart z = 0) (him : realPart (Complex.I • z) = 0) : z = 0 := by
  let e := TensorProduct.mk ℝ ℂ V 1
  let mulI : ℂ ⊗[ℝ] V →ₗ[ℝ] ℂ ⊗[ℝ] V :=
    (Complex.I • (LinearMap.id : Module.End ℂ (ℂ ⊗[ℝ] V))).restrictScalars ℝ
  have hdecomp : e.comp realPart - mulI.comp (e.comp (realPart.comp mulI)) = LinearMap.id := by
    apply TensorProduct.ext'
    intro c v
    change (1 : ℂ) ⊗ₜ[ℝ] (realPart (c ⊗ₜ[ℝ] v)) -
      Complex.I • ((1 : ℂ) ⊗ₜ[ℝ] (realPart (Complex.I • (c ⊗ₜ[ℝ] v))))
      = c ⊗ₜ[ℝ] v
    have himag : realPart (Complex.I • (c ⊗ₜ[ℝ] v)) = -(c.im • v) := by
      rw [TensorProduct.smul_tmul', realPart_tmul, smul_eq_mul, Complex.I_mul_re, neg_smul]
    rw [himag, realPart_tmul, TensorProduct.tmul_neg, smul_neg, sub_neg_eq_add,
      ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul',
      ← TensorProduct.add_tmul]
    simp only [Complex.real_smul, smul_eq_mul, mul_one]
    rw [mul_comm Complex.I, Complex.re_add_im]
  have hz : e (realPart z) - Complex.I • e (realPart (Complex.I • z)) = z :=
    LinearMap.congr_fun hdecomp z
  simpa only [hre, him, map_zero, smul_zero, sub_zero] using hz.symm

/-- The square of an irreducible real degree is at most four times the order. -/
theorem real_irreducible_finrank_sq_le_four_card [Monoid H] [Finite H]
    [FiniteDimensional ℝ V] (ρ : Representation ℝ H V) [ρ.IsIrreducible] :
    Module.finrank ℝ V ^ 2 ≤ 4 * Nat.card H := by
  classical
  let : Fintype H := Fintype.ofFinite H
  have : Nontrivial V :=
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.nontrivial
      (ρ := ρ) inferInstance
  have : Nontrivial (ℂ ⊗[ℝ] V) := Module.nontrivial_of_finrank_pos (R := ℂ)
    (by rw [Module.finrank_baseChange]; exact Module.finrank_pos)
  obtain ⟨U, hU⟩ := TauCeti.Representation.exists_isAtom (complexification ρ)
  have hsimple := TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom hU
  have : Nontrivial U.toSubmodule :=
    D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.nontrivial hsimple
  have : FiniteDimensional ℝ U.toSubmodule := FiniteDimensional.trans ℝ ℂ U.toSubmodule
  let f : U.toSubmodule →ₗ[ℝ] V := realPart.comp (U.toSubmodule.subtype.restrictScalars ℝ)
  let W : Subrepresentation ρ :=
    ⟨LinearMap.range f, by
      rintro g _ ⟨u, rfl⟩
      exact ⟨U.toRepresentation g u, realPart_equivariant ρ g u⟩⟩
  have hW : W ≠ ⊥ := by
    intro hbot
    have hf (u : U.toSubmodule) : f u = 0 := by
      have hu : f u ∈ W := ⟨u, rfl⟩
      rw [hbot] at hu
      exact (Submodule.mem_bot ℝ).mp hu
    obtain ⟨u, hu⟩ := exists_ne (0 : U.toSubmodule)
    apply hu
    apply Subtype.ext
    exact eq_zero_of_realPart_of_I (u : ℂ ⊗[ℝ] V) (hf u)
      (by simpa only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.subtype_apply, Submodule.coe_smul] using hf (Complex.I • u))
  have hsurj : Function.Surjective f := by
    have ht := (eq_bot_or_eq_top W).resolve_left hW
    exact LinearMap.range_eq_top.mp (congrArg Subrepresentation.toSubmodule ht)
  have hreal := LinearMap.finrank_le_finrank_of_surjective hsurj
  rw [← Module.finrank_mul_finrank ℝ ℂ U.toSubmodule, Complex.finrank_real_complex] at hreal
  have hcomplex : Module.finrank ℂ U.toSubmodule ^ 2 ≤ Nat.card H := by
    have hdensity := asAlgebraHom_surjective_of_isIrreducible U.toRepresentation hsimple
    have h := LinearMap.finrank_le_finrank_of_surjective
      (f := U.toRepresentation.asAlgebraHom.toLinearMap) hdensity
    have hcard : Module.finrank ℂ (MonoidAlgebra ℂ H) = Nat.card H := by
      rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis H ℂ), Fintype.card_eq_nat_card]
    simpa only [Module.finrank_linearMap, hcard, pow_two] using h
  calc
    Module.finrank ℝ V ^ 2 ≤ (2 * Module.finrank ℂ U.toSubmodule) ^ 2 :=
      Nat.pow_le_pow_left hreal 2
    _ = 4 * Module.finrank ℂ U.toSubmodule ^ 2 := by
      rw [mul_pow, show (2 : ℕ) ^ 2 = 4 by decide]
    _ ≤ 4 * Nat.card H := Nat.mul_le_mul_left 4 hcomplex

/-- The small normal-factor case of P48p forces a proper nonzero real invariant
subspace in dimension 48. Only the order and index bounds are needed. -/
theorem p48p_small_factor_exists_real_invariant_subspace [Group H] [Finite H]
    [FiniteDimensional ℝ V] (K : Subgroup H) (ρ : Representation ℝ H V)
    (hdim : Module.finrank ℝ V = 48) (hK : Nat.card K ≤ 16) (hindex : K.index ∣ 12) :
    ∃ W : Submodule ℝ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g, W ≤ W.comap (ρ g) := by
  classical
  have hH : Nat.card H ≤ 192 := by
    rw [← K.card_mul_index]
    exact Nat.mul_le_mul hK (Nat.le_of_dvd (by decide) hindex)
  by_contra h
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; decide)
  have : Nontrivial (Subrepresentation ρ) :=
    nontrivial_of_ne ⊥ ⊤ (fun he => bot_ne_top (congrArg Subrepresentation.toSubmodule he))
  have : ρ.IsIrreducible := ⟨fun W => by
    by_contra hw
    push Not at hw
    apply h
    refine ⟨W.toSubmodule, ?_, ?_, fun g _ hv => W.apply_mem_toSubmodule g hv⟩
    · exact fun he => hw.1 (Subrepresentation.toSubmodule_injective he)
    · exact fun he => hw.2 (Subrepresentation.toSubmodule_injective he)⟩
  have hbound := real_irreducible_finrank_sq_le_four_card ρ
  rw [hdim] at hbound
  omega

#print axioms real_irreducible_finrank_sq_le_four_card
#print axioms p48p_small_factor_exists_real_invariant_subspace

end ExtremalC48
