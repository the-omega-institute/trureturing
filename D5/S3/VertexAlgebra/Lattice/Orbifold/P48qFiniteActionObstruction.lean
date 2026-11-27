/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFiniteActionObstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qFiniteActionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite conformal actions on P48q have fixed quadratics or a cubic weight obstruction. -/

/- Source: Library/VertexAlgebra/nebe2014extremal48.md. -/

import D5.S3.FiniteGroups.Cyclic.SL47OddOrderRationalReducibility
import D5.S3.VertexAlgebra.Lattice.Automorphisms.ConformalGroundTransport
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNonsplitActionObstruction
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSplitActionObstruction
import Mathlib.LinearAlgebra.Reflection
import OmegaBuild.Commands

/-!
The exhaustive faithful charge realization rules out norm-two roots, whose
reflections would give involutions distinct from charge negation.
The projected subgroup supplies an actual cubic lift when its order is
divisible by six. In the other cases its rational Cartan action has a
proper nonzero invariant block. The block and its orthogonal complement
supply fixed quadratics for the original conformal action.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteActionObstruction

open LatticeGeneratingFieldLocality (Charge Carrier bilinear unitCharge)
open LatticeActualGeneratorLocality (bilinear_add_right)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open LatticeActualConformalState (omega)
open LatticePositiveEnergy (grade)
open LatticeSugawaraCurrents (gramComplex)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left)
open Lattice.Automorphisms.ConformalGroundTransport (conformal_ground_projection)
open DiagonalCharacterConjugacy (PreservesModes ground)
open ExtremalC48 (SL47 sl47_odd_order_exists_invariant_subspace
  sl47_prime_to_three_exists_invariant_subspace)
open P48qGramCertificate (gram_inverse_certificate)
open P48qGramPositivity (nebeGram_posDef)
open P48qInvariantQuadratics (RationalCartan rationalGram blockQuadratic invariant_block_quadratics)
open P48qNonsplitActionObstruction (p48q_orderThree_lift_of_even_range)
open P48qOrderThreeSpectrumTransport (CubicTwistedModuleLaw conformalZeroMode
  actual_twisted_spectrum_of_order_three_isometry)
open P48qTwistedChargeAction (lattice)
open scoped Matrix VertexOperator

open private bilinear_sub_left bilinear_sub_right from
  D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open private sl47_orderTwo_eq_neg_one p48q_neg_one_charge from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNonsplitActionObstruction
open private rationalAction rationalAction_injective rationalExtension_preserves_gram
  rationalCurrent_lift from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSplitActionObstruction

universe u

private theorem p48q_rootless_of_exhaustive
    (realization : Additive SL47 →+ AddAut (Charge lattice))
    (hFaithful : Function.Injective realization)
    (hExhaustive : ∀ s : AddAut (Charge lattice),
      (∀ a b, bilinear lattice (s a) (s b) = bilinear lattice a b) → ∃ k, realization k = s) :
    ∀ r : Charge lattice, bilinear lattice r r ≠ 2 := by
  intro r hr
  have hSmulLeft (c : ℤ) (a b : Charge lattice) :
      bilinear lattice (c • a) b = c * bilinear lattice a b := by
    simp only [bilinear, Pi.smul_apply, Int.zsmul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hSmulRight (c : ℤ) (a b : Charge lattice) :
      bilinear lattice a (c • b) = c * bilinear lattice a b := by
    rw [bilinear_symmetric lattice a (c • b), hSmulLeft, bilinear_symmetric lattice b a]
  let pairing : Module.Dual ℤ (Charge lattice) :=
    { toFun := fun a => bilinear lattice a r
      map_add' := fun a b => by
        rw [bilinear_symmetric lattice (a + b) r, bilinear_add_right,
          bilinear_symmetric lattice r a, bilinear_symmetric lattice r b]
      map_smul' := fun c a => hSmulLeft c a r }
  have hNorm : pairing r = 2 := hr
  let s : AddAut (Charge lattice) := (Module.reflection hNorm).toAddEquiv
  have hApply (a : Charge lattice) : s a = a - bilinear lattice a r • r := by
    change Module.reflection hNorm a = a - pairing a • r
    rw [Module.reflection_apply]
  have hPreserves (a b : Charge lattice) :
      bilinear lattice (s a) (s b) = bilinear lattice a b := by
    simp only [hApply, bilinear_sub_left, bilinear_sub_right, hSmulLeft, hSmulRight, hr,
      bilinear_symmetric lattice r b]
    ring
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hOrder : addOrderOf s = 2 := by
    apply addOrderOf_eq_prime
    · rw [two_nsmul]
      apply AddEquiv.ext
      intro a
      change Module.reflection hNorm (Module.reflection hNorm a) = a
      exact Module.involutive_reflection hNorm a
    · intro hIdentity
      have h := DFunLike.congr_fun hIdentity r
      change Module.reflection hNorm r = r at h
      rw [Module.reflection_apply_self] at h
      have hZero : r = 0 := by
        funext i
        have hi := congrFun h i
        change -(r i) = r i at hi
        change r i = 0
        omega
      rw [hZero] at hr
      norm_num [bilinear] at hr
  obtain ⟨k, hk⟩ := hExhaustive s hPreserves
  let chargeAction := realization.toMultiplicativeRight
  have hOrderK : orderOf k.toMul = 2 := by
    rw [← orderOf_injective chargeAction (Multiplicative.ofAdd.injective.comp hFaithful) k.toMul]
    change addOrderOf (realization k) = 2
    rw [hk, hOrder]
  have hNegK := sl47_orderTwo_eq_neg_one k.toMul hOrderK
  have hNeg (a : Charge lattice) : s a = -a := by
    rw [← hk]
    change realization (Additive.ofMul k.toMul) a = -a
    rw [hNegK]
    exact p48q_neg_one_charge realization hFaithful hExhaustive a
  have hCoordinate (i j : Fin lattice.rank) :
      bilinear lattice (unitCharge lattice i) r * r j = 2 * unitCharge lattice i j := by
    have h := congrFun (hNeg (unitCharge lattice i)) j
    simp only [hApply, Pi.sub_apply, Pi.smul_apply, Int.zsmul_eq_mul, Pi.neg_apply] at h
    omega
  let i0 : Fin lattice.rank := (0 : Fin 48)
  let i1 : Fin lattice.rank := (1 : Fin 48)
  have h10 : i1 ≠ i0 := by
    change (1 : Fin 48) ≠ 0
    decide
  have h00 : bilinear lattice (unitCharge lattice i0) r * r i0 = 2 := by
    simpa only [show unitCharge lattice i0 i0 = 1 by simp [unitCharge], mul_one]
      using hCoordinate i0 i0
  have hPair : bilinear lattice (unitCharge lattice i0) r ≠ 0 := by
    intro hZero
    norm_num [hZero] at h00
  have h01 : bilinear lattice (unitCharge lattice i0) r * r i1 = 0 := by
    simpa only [show unitCharge lattice i0 i1 = 0 by simp [unitCharge, h10], mul_zero]
      using hCoordinate i0 i1
  have hr1 : r i1 = 0 := (mul_eq_zero.mp h01).resolve_left hPair
  have h11 := hCoordinate i1 i1
  have hDiag : unitCharge lattice i1 i1 = 1 := by simp [unitCharge]
  norm_num [hr1, hDiag] at h11

/-- A faithful finite conformal action has two independent fixed weight-two
states or an actual cubic element projecting to an order-three isometry with
nonintegral weights in every admissible cubic twisted field. -/
theorem p48q_finite_action_obstruction
    (realization : Additive SL47 →+ AddAut (Charge lattice))
    (hFaithful : Function.Injective realization)
    (hIsometry : ∀ s : Additive SL47, ∀ a b,
      bilinear lattice (realization s a) (realization s b) = bilinear lattice a b)
    (hExhaustive : ∀ s : AddAut (Charge lattice),
      (∀ a b, bilinear lattice (s a) (s b) = bilinear lattice a b) → ∃ k, realization k = s)
    {E : Type*} [Group E] [Finite E]
    (U : E →* (Carrier lattice ≃ₗ[ℂ] Carrier lattice))
    (hU : Function.Injective U) (hMode : ∀ e, PreservesModes lattice (U e))
    (hOmega : ∀ e, U e (omega lattice (actualInverse lattice)) =
      omega lattice (actualInverse lattice)) :
    ∃ (π : E →* SL47) (phase : E → Charge lattice → ℂˣ),
      (∀ e a, U e (ground lattice a) =
        (phase e a : ℂ) • ground lattice (realization (Additive.ofMul (π e)) a)) ∧
      ((∃ q : Fin 2 → Carrier lattice, (∀ i, q i ∈ grade lattice 2) ∧
          (∀ e i, U e (q i) = q i) ∧ LinearIndependent ℂ q) ∨
        (∃ e : E, orderOf e = 3 ∧ addOrderOf (realization (Additive.ofMul (π e))) = 3 ∧
          ∀ (W : Type u) [AddCommGroup W] [Module ℂ W]
            (Ytw : Carrier lattice →ₗ[ℂ] VertexOperator ℂ W), CubicTwistedModuleLaw (U e) Ytw →
            ∀ lower : ℝ,
              (∀ (r : ℂ) (v : W), v ≠ 0 → conformalZeroMode Ytw v = r • v → lower ≤ r.re) →
              (∀ r : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (conformalZeroMode Ytw) r)) →
              ∀ (r : ℂ) (v : W), v ≠ 0 → conformalZeroMode Ytw v = r • v →
                (∃ n : ℕ, r = 16 / 9 + (n : ℂ) / 3) ∧
                (∃ m : ℤ, 9 * r = (m : ℂ) ∧ m % 3 = 1) ∧ ∀ z : ℤ, r ≠ (z : ℂ))) := by
  have hRoot := p48q_rootless_of_exhaustive realization hFaithful hExhaustive
  have hInverse : actualInverse lattice * gramComplex lattice = 1 :=
    actualInverse_left lattice (Matrix.isUnit_det_of_left_inverse gram_inverse_certificate)
  obtain ⟨π, phase, hTransport⟩ := conformal_ground_projection lattice nebeGram_posDef
    hRoot (actualInverse lattice) hInverse realization hFaithful hExhaustive U
    (fun e a n b => hMode e a b n) hOmega
  have hGround (e : E) (a : Charge lattice) : U e (ground lattice a) =
      (phase e a : ℂ) • ground lattice (realization (Additive.ofMul (π e)) a) :=
    hTransport e a
  refine ⟨π, phase, hGround, ?_⟩
  let H := π.range
  letI : Finite H := Finite.of_surjective π.rangeRestrict π.rangeRestrict_surjective
  by_cases hCubic : (2 ∣ Nat.card H) ∧ (3 ∣ Nat.card H)
  · obtain ⟨e, hOrder, hChargeOrder⟩ := p48q_orderThree_lift_of_even_range
      realization hFaithful hExhaustive π U phase hU hMode hGround hCubic.1 hCubic.2
    have hCube : U e ^ (3 : ℕ) = 1 := by
      rw [← map_pow, ← hOrder, pow_orderOf_eq_one, map_one]
    refine Or.inr ⟨e, hOrder, hChargeOrder, ?_⟩
    intro W _ _ Ytw hY lower hLower hFinite r v hv hr
    exact actual_twisted_spectrum_of_order_three_isometry realization hFaithful hIsometry
      hExhaustive _ (hIsometry (Additive.ofMul (π e))) hChargeOrder (U e) (phase e)
      (hGround e) (hMode e) hCube Ytw hY lower hLower hFinite r v hv hr
  · let chargeAction := realization.toMultiplicativeRight.comp H.subtype
    have hChargeInj : Function.Injective chargeAction :=
      Multiplicative.ofAdd.injective.comp (hFaithful.comp
        (Additive.ofMul.injective.comp Subtype.val_injective))
    let ρ : Representation ℚ H (RationalCartan lattice) :=
      (rationalAction lattice).comp chargeAction
    have hρ : Function.Injective ρ := (rationalAction_injective lattice).comp hChargeInj
    have hDim : Module.finrank ℚ (RationalCartan lattice) = 48 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] <;> rfl
    have hBlock : ∃ W : Submodule ℚ (RationalCartan lattice),
        W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ h, W ≤ W.comap (ρ h) := by
      by_cases hEven : 2 ∣ Nat.card H
      · exact sl47_prime_to_three_exists_invariant_subspace H
          (fun hThree => hCubic ⟨hEven, hThree⟩) ρ hρ hDim
      · exact sl47_odd_order_exists_invariant_subspace H hEven ρ hρ hDim
    obtain ⟨W, hBot, hTop, hW⟩ := hBlock
    let A : Representation ℂ E (Carrier lattice) :=
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp U
    refine Or.inl ⟨![blockQuadratic lattice nebeGram_posDef W,
      blockQuadratic lattice nebeGram_posDef ((rationalGram lattice).orthogonal W)], ?_⟩
    exact invariant_block_quadratics lattice nebeGram_posDef (ρ.comp π.rangeRestrict) A
      (fun e => rationalExtension_preserves_gram lattice _ (hIsometry (Additive.ofMul (π e))))
      (fun e => rationalCurrent_lift lattice _ (hIsometry (Additive.ofMul (π e)))
        (U e) (phase e) (hMode e) (hGround e))
      (fun e a n b => hMode e a b n) W hBot hTop (fun e => hW (π.rangeRestrict e))

#print axioms p48q_finite_action_obstruction

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteActionObstruction
