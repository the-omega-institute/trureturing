/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qHolomorphicExtensionObstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qHolomorphicExtensionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sector-compatible integral extensions for P48q have weight-two dimension at least two. -/

import D5.S3.FiniteGroups.TwistedFixedCosetSections
import D5.S3.VertexAlgebra.Lattice.Orbifold.InducedVacuumBranching
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteActionObstruction
import OmegaMath.LinearAlgebra.Eigenspace.Intertwining
import OmegaBuild.Commands

/-!
The extension realization enters through a weight-two-preserving inclusion of
the actual fixed states and conformal inclusions of nonzero cubic branches.
For the identity branch, the linear equivalence
`InducedVacuumBranching.evaluate` identifies the induced-vacuum multiplicity
space with the fixed states, and `InducedVacuumBranching.evaluate_mem_grade_iff`
identifies their grades for a grading-preserving action. A realization of that
branch supplies the fixed-state inclusion via inverse evaluation.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHolomorphicExtensionObstruction

open FiniteGroups.FixedCosetBranching (ConjugatingElements)
open FiniteGroups.TwistedFixedCosetSections
  (degreeSections exists_section_identity_support transportOfCochain)
open ExtremalC48 (SL47)
open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open LatticeGeneratingFieldLocality (Carrier Charge bilinear)
open LatticePositiveEnergy (grade)
open DiagonalCharacterConjugacy (PreservesModes)
open P48qFiniteActionObstruction (p48q_finite_action_obstruction)
open P48qOrderThreeSpectrumTransport (CubicTwistedModuleLaw conformalZeroMode)
open P48qTwistedChargeAction (lattice)
open scoped VertexOperator

universe u v

local notation "V" => Carrier lattice
local notation "fixedStates(" U ", " K ")" =>
  Representation.invariants
    (MonoidHom.comp (MonoidHom.comp LinearEquiv.automorphismGroup.toLinearMapMonoidHom U)
      (Subgroup.subtype K))

/-- The conformal data of a realized cubic branch. The field uses the actual
lattice states and satisfies the cubic vacuum, residue, Borcherds and translation
laws. Its chosen submodule is stable under the field's conformal zero mode. -/
structure CubicSectorRealization (lift : V ≃ₗ[ℂ] V) {W : Type v}
    [AddCommGroup W] [Module ℂ W] (L_W : Module.End ℂ W) where
  space : Type u
  [spaceAdd : AddCommGroup space]
  [spaceModule : Module ℂ space]
  field : V →ₗ[ℂ] VertexOperator ℂ space
  fieldLaw : CubicTwistedModuleLaw lift field
  lower : ℝ
  lowerBound : ∀ (r : ℂ) (x : space), x ≠ 0 →
    conformalZeroMode field x = r • x → lower ≤ r.re
  finiteWeight : ∀ r : ℂ, FiniteDimensional ℂ ((conformalZeroMode field).eigenspace r)
  branch : Submodule ℂ space
  nonzero : branch ≠ ⊥
  stable : ∀ x ∈ branch, conformalZeroMode field x ∈ branch
  inclusion : branch →ₗ[ℂ] W
  injective : Function.Injective inclusion
  intertwines : ∀ x : branch,
    inclusion (LinearMap.restrict (conformalZeroMode field) stable x) = L_W (inclusion x)

/-- A sector-compatible extension realization for the actual P48q lattice
action has at least two weight-two states. The target is spanned by its integer
eigenspaces, and only its weight-two eigenspace is assumed finite-dimensional.
The cubic premise is triggered by a nonzero degree section for the specified
ambient cocycle and subgroup trivializing cochain. -/
theorem p48q_holomorphic_extension_obstruction
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
    (hNormalized : ∀ a b c, (a = 1 ∨ b = 1 ∨ c = 1) → α a b c = 1)
    (hCocycle : ∀ a b c d, α b c d * α a (b * c) d * α a b c =
      α (a * b) c d * α a b (c * d))
    (hCochainNormalized : ∀ a b : K, (a = 1 ∨ b = 1) → γ a b = 1)
    (hRestricted : ∀ a b c : K, α a b c = γ b c * γ a (b * c) / (γ (a * b) c * γ a b))
    {W : Type v} [AddCommGroup W] [Module ℂ W] (L_W : Module.End ℂ W)
    (hGraded : (⨆ n : ℤ, L_W.eigenspace (n : ℂ)) = ⊤)
    [FiniteDimensional ℂ (L_W.eigenspace (2 : ℂ))]
    (vacuumInclusion : fixedStates(U, K) →ₗ[ℂ] W)
    (hVacuumInjective : Function.Injective vacuumInclusion)
    (hVacuumWeight : ∀ x : fixedStates(U, K), (x : V) ∈ grade lattice 2 →
      vacuumInclusion x ∈ L_W.eigenspace (2 : ℂ))
    (hCubic : ∀ g : G, orderOf g = 3 →
      (∃ f : degreeSections (transportOfCochain (g := g) α γ hNormalized hCocycle
        hCochainNormalized hRestricted), f ≠ 0) →
      Nonempty (CubicSectorRealization.{u, v} (U g) L_W)) :
    2 ≤ Module.finrank ℂ (L_W.eigenspace (2 : ℂ)) := by
  obtain ⟨_, _, _, hDichotomy⟩ :=
    p48q_finite_action_obstruction.{u} realization hFaithful hIsometry hExhaustive
      (U.comp K.subtype) (hU.comp Subtype.val_injective)
      (fun k => hMode k) (fun k => hOmega k)
  rcases hDichotomy with ⟨q, hGrade, hFixed, hIndependent⟩ | ⟨k, hOrder, _, hSpectrum⟩
  · let qFixed (i : Fin 2) : fixedStates(U, K) := ⟨q i, fun k => hFixed k i⟩
    have hFixedIndependent : LinearIndependent ℂ qFixed :=
      LinearIndependent.of_comp fixedStates(U, K).subtype hIndependent
    let qImage (i : Fin 2) : L_W.eigenspace (2 : ℂ) :=
      ⟨vacuumInclusion (qFixed i), hVacuumWeight (qFixed i) (hGrade i)⟩
    have hImageIndependent : LinearIndependent ℂ qImage := by
      apply LinearIndependent.of_comp (L_W.eigenspace (2 : ℂ)).subtype
      exact hFixedIndependent.map' vacuumInclusion (LinearMap.ker_eq_bot.mpr hVacuumInjective)
    simpa only [Fintype.card_fin] using hImageIndependent.fintype_card_le_finrank
  · let g : G := k
    have hg : g ∈ K := k.property
    have hOrderG : orderOf g = 3 :=
      (orderOf_injective K.subtype Subtype.val_injective k).trans hOrder
    let transport := transportOfCochain (g := g) α γ hNormalized hCocycle
      hCochainNormalized hRestricted
    obtain ⟨f, hSupport⟩ := exists_section_identity_support transport hg
    let identityLift : ConjugatingElements K g :=
      ⟨1, by simpa only [inv_one, one_mul, mul_one] using hg⟩
    have hNonzero : f ≠ 0 := by
      have hAtIdentity := (hSupport identityLift).mpr rfl
      intro hf
      exact hAtIdentity (congrArg (fun s : degreeSections transport => s.val identityLift) hf)
    obtain ⟨sector⟩ := hCubic g hOrderG ⟨f, hNonzero⟩
    let _ := sector.spaceAdd
    let _ := sector.spaceModule
    let L : Module.End ℂ sector.branch :=
      LinearMap.restrict (conformalZeroMode sector.field) sector.stable
    have hNoEigenvalue (n : ℤ) : ¬ L.HasEigenvalue (n : ℂ) := by
      intro hEigenvalue
      obtain ⟨x, hx⟩ := hEigenvalue.exists_hasEigenvector
      have hxNonzero : (x : sector.space) ≠ 0 := fun h =>
        (Module.End.hasEigenvector_iff.mp hx).2 (Subtype.ext h)
      have hxEigen :
          conformalZeroMode sector.field (x : sector.space) = (n : ℂ) • (x : sector.space) := by
        simpa only [L, LinearMap.coe_restrict_apply, Submodule.coe_smul] using
          congrArg (fun y : sector.branch => (y : sector.space)) hx.apply_eq_smul
      exact (hSpectrum sector.space sector.field sector.fieldLaw sector.lower sector.lowerBound
        sector.finiteWeight (n : ℂ) x hxNonzero hxEigen).2.2 n rfl
    have hVanish := Omega.LinearAlgebra.eq_zero_of_injective_intertwiner_of_no_eigenvalue
      L L_W (fun n : ℤ => (n : ℂ)) hGraded hNoEigenvalue
      sector.inclusion sector.injective sector.intertwines
    obtain ⟨x, hx, hxNonzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot sector.nonzero
    exact (hxNonzero
      (congrArg (fun y : sector.branch => (y : sector.space)) (hVanish ⟨x, hx⟩))).elim

#print axioms p48q_holomorphic_extension_obstruction

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHolomorphicExtensionObstruction
