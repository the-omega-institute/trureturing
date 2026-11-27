/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qAssociatorExtensionObstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qAssociatorExtensionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The type-one ambient associator obstructs extremal P48q extensions. -/

import D5.S3.FiniteGroups.Cyclic.CyclicAssociatorObstruction
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteActionObstruction
import OmegaBuild.Commands

/-!
Evans–Gannon, arXiv:1804.11145, equation (2.13), use the cyclic carry
representative with phase `exp(2πi/n)`. By equation (2.14) the weight in
generator flux is congruent to `q/n²` modulo `1/n`, after removing the central
charge contribution. The P48q spectral residue `16/9` modulo `1/3` therefore
selects `q = 1` in that convention. The comparison of the actual ambient
associator with this representative is an external hypothesis.

The inclusion of fixed states uses the vacuum inclusion interface of
`P48qHolomorphicExtensionObstruction.p48q_holomorphic_extension_obstruction`.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qAssociatorExtensionObstruction

open FiniteGroups.Cyclic.CyclicAssociatorObstruction
  (carryPhase cyclicPowerHom not_mem_of_nonzero_type twoCoboundary)
open ExtremalC48 (SL47)
open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open LatticeGeneratingFieldLocality (Carrier Charge bilinear)
open LatticePositiveEnergy (grade)
open DiagonalCharacterConjugacy (PreservesModes ground)
open P48qFiniteActionObstruction (p48q_finite_action_obstruction)
open P48qTwistedChargeAction (lattice)

local notation "V" => Carrier lattice
local notation "fixedStates(" U ", " K ")" =>
  Representation.invariants
    (MonoidHom.comp (MonoidHom.comp LinearEquiv.automorphismGroup.toLinearMapMonoidHom U)
      (Subgroup.subtype K))

/-- An injective weight-two-preserving inclusion of the P48q fixed states
forces target weight-two dimension at least two. The subgroup may be any
subgroup whose cochain trivializes the ambient associator. For each ambient
order-three element with an order-three charge isometry, the external type
comparison identifies the associator pullback with type one up to a
two-coboundary. -/
theorem p48q_associator_extension_obstruction
    (realization : Additive SL47 →+ AddAut (Charge lattice))
    (hFaithful : Function.Injective realization)
    (hIsometry : ∀ s : Additive SL47, ∀ a b,
      bilinear lattice (realization s a) (realization s b) = bilinear lattice a b)
    (hExhaustive : ∀ s : AddAut (Charge lattice),
      (∀ a b, bilinear lattice (s a) (s b) = bilinear lattice a b) → ∃ k, realization k = s)
    {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (U : G →* (V ≃ₗ[ℂ] V))
    (hU : Function.Injective U) (hMode : ∀ g, PreservesModes lattice (U g))
    (hOmega : ∀ g, U g (omega lattice (actualInverse lattice)) =
      omega lattice (actualInverse lattice))
    (α : G → G → G → ℂˣ) (γ : K → K → ℂˣ)
    (hRestricted : ∀ a b c : K, α a.val b.val c.val = twoCoboundary γ a b c)
    (ζ : ℂˣ) (hζ : orderOf ζ = 3)
    (hType : ∀ (g : G) (hg : orderOf g = 3) (s : Additive SL47)
      (phase : Charge lattice → ℂˣ), addOrderOf (realization s) = 3 →
      (∀ a, U g (ground lattice a) = (phase a : ℂ) • ground lattice (realization s a)) →
      ∃ β : Multiplicative (ZMod 3) → Multiplicative (ZMod 3) → ℂˣ,
        ∀ a b c, α (cyclicPowerHom g hg a) (cyclicPowerHom g hg b) (cyclicPowerHom g hg c) =
          carryPhase ζ hζ (1 : ZMod 3) a b c * twoCoboundary β a b c)
    {W : Type*} [AddCommGroup W] [Module ℂ W] (L_W : Module.End ℂ W)
    [FiniteDimensional ℂ (L_W.eigenspace (2 : ℂ))]
    (vacuumInclusion : fixedStates(U, K) →ₗ[ℂ] W)
    (hVacuumInjective : Function.Injective vacuumInclusion)
    (hVacuumWeight : ∀ x : fixedStates(U, K), (x : V) ∈ grade lattice 2 →
      vacuumInclusion x ∈ L_W.eigenspace (2 : ℂ)) :
    2 ≤ Module.finrank ℂ (L_W.eigenspace (2 : ℂ)) := by
  obtain ⟨π, phase, hGround, hDichotomy⟩ :=
    p48q_finite_action_obstruction.{0} realization hFaithful hIsometry hExhaustive
      (U.comp K.subtype) (hU.comp Subtype.val_injective)
      (fun k => hMode k) (fun k => hOmega k)
  rcases hDichotomy with ⟨q, hGrade, hFixed, hIndependent⟩ | ⟨k, hOrder, hChargeOrder, _⟩
  · let qFixed (i : Fin 2) : fixedStates(U, K) := ⟨q i, fun k => hFixed k i⟩
    have hFixedIndependent : LinearIndependent ℂ qFixed :=
      LinearIndependent.of_comp fixedStates(U, K).subtype hIndependent
    let qImage (i : Fin 2) : L_W.eigenspace (2 : ℂ) :=
      ⟨vacuumInclusion (qFixed i), hVacuumWeight (qFixed i) (hGrade i)⟩
    have hImageIndependent : LinearIndependent ℂ qImage :=
      LinearIndependent.of_comp (L_W.eigenspace (2 : ℂ)).subtype
        (hFixedIndependent.map' vacuumInclusion (LinearMap.ker_eq_bot.mpr hVacuumInjective))
    simpa only [Fintype.card_fin] using hImageIndependent.fintype_card_le_finrank
  · let g : G := K.subtype k
    have hg : orderOf g = 3 :=
      (orderOf_injective K.subtype Subtype.val_injective k).trans hOrder
    obtain ⟨β, hCompare⟩ :=
      hType g hg (Additive.ofMul (π k)) (phase k) hChargeOrder (hGround k)
    exact (not_mem_of_nonzero_type (by decide) α g hg ζ hζ (1 : ZMod 3)
      (by decide) β hCompare K γ hRestricted k.property).elim

#print axioms p48q_associator_extension_obstruction

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qAssociatorExtensionObstruction
