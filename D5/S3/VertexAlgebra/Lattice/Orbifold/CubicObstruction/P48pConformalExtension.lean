/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pConformalExtension
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pConformalExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual conformal action on a rootless P48p lattice supplies the charge projection for the extension obstruction. -/

import D5.S3.VertexAlgebra.Lattice.Automorphisms.ConformalGroundTransport
import D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.P48pDerivedExtension
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.P48pConformalExtension

open Automorphisms.ConformalGroundTransport (conformal_ground_projection)
open Automorphisms.ReducibleActionWeightTwo (realChargeRepresentation)
open DiagonalCharacterConjugacy (PreservesModes ground)
open FiniteGroups.Cyclic.CyclicAssociatorObstruction (carryPhase cyclicPowerHom twoCoboundary)
open LatticeActualConformalState (omega)
open LatticeGeneratingFieldLocality (LatticeData Carrier Charge bilinear)
open LatticePositiveEnergy (grade)
open LatticeSugawaraCurrents (gramComplex)
open P48pDerivedExtension (p48p_associator_extension_obstruction_of_derived_action)

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 23)
local notation "fixedCartan(" D ", " charge ", " g ")" =>
  LinearMap.ker (realChargeRepresentation D (charge g) - 1)
local notation "fixedStates(" U ", " K ")" =>
  Representation.invariants
    (MonoidHom.comp (MonoidHom.comp LinearEquiv.automorphismGroup.toLinearMapMonoidHom U)
      (Subgroup.subtype K))

/-- On a rootless rank-48 lattice with the P48p charge data, the actual conformal
action on the fixed-sector subgroup recovers the charge transport needed for
the extension obstruction. The comparison with the ambient associator is
assumed for each actual standard rank-sixteen cubic. -/
theorem p48p_associator_extension_obstruction_of_conformal_action
    (D : LatticeData) (hRank : D.rank = 48)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hRoot : ∀ a : Charge D, bilinear D a a ≠ 2)
    (inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hInverse : inverse * gramComplex D = 1)
    {A : Type*} [Group A] [Finite A] (N L : Subgroup A) [N.Normal] (hNL : N ≤ L)
    (hCard : Nat.card N ∣ 2 ^ 4 * 3 * 11 * 23) (hIndex : N.index ∣ 12)
    (φ : N →* SL23) (hφ : Function.Injective φ)
    (charge : A →* Multiplicative (AddAut (Charge D))) (hCharge : Function.Injective charge)
    (hIsometry : ∀ g : A, ∀ a b,
      bilinear D ((charge g).toAdd a) ((charge g).toAdd b) = bilinear D a b)
    (hExhaustive : ∀ t : AddAut (Charge D),
      (∀ a b, bilinear D (t a) (t b) = bilinear D a b) → ∃ g : A, (charge g).toAdd = t)
    (ρ : Representation ℚ L (Fin D.rank → ℚ)) [ρ.IsIrreducible]
    (hρ : ∀ (g : L) (a : Charge D), ρ g (fun i => (a i : ℚ)) =
      fun i => ((charge (g : A)).toAdd a i : ℚ))
    (s : N) (hs : orderOf s = 2) (hsImage : φ s = -(1 : SL23))
    (hsCentral : Subgroup.inclusion hNL s ∈ Subgroup.center L)
    (c : L) (hc : orderOf c = 3) (hcCentral : c ∈ Subgroup.center L)
    (hcOutside : (c : A) ∉ N)
    (hAllowed : ∀ g : L, orderOf g = 3 →
      Module.finrank ℝ (fixedCartan(D, charge, (g : A))) = 0 ∨
      Module.finrank ℝ (fixedCartan(D, charge, (g : A))) = 16)
    (hFixedEleven : ∀ n : N, orderOf n = 11 →
      Module.finrank ℝ (fixedCartan(D, charge, (n : A))) = 8)
    (hFixedTwentyThree : ∀ n : N, orderOf n = 23 →
      Module.finrank ℝ (fixedCartan(D, charge, (n : A))) = 4)
    {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (U : G →* (Carrier D ≃ₗ[ℂ] Carrier D)) (hU : Function.Injective U)
    (hMode : ∀ k : K, PreservesModes D (U k))
    (hOmega : ∀ k : K, U k (omega D inverse) = omega D inverse)
    (α : G → G → G → ℂˣ) (γ : K → K → ℂˣ)
    (hRestricted : ∀ a b c : K, α a.val b.val c.val = twoCoboundary γ a b c)
    (ζ : ℂˣ) (hζ : orderOf ζ = 3)
    (hType : ∀ (k : K) (hk : orderOf (k : G) = 3) (g : A) (phase : Charge D → ℂˣ),
      orderOf (charge g) = 3 →
      Module.finrank ℝ (fixedCartan(D, charge, g)) = 16 →
      (∀ a, U k (ground D a) = (phase a : ℂ) • ground D ((charge g).toAdd a)) →
      (∀ a, (charge g).toAdd a = a → phase a = 1) →
      ∃ β : Multiplicative (ZMod 3) → Multiplicative (ZMod 3) → ℂˣ,
        ∀ a b c, α (cyclicPowerHom (k : G) hk a) (cyclicPowerHom (k : G) hk b)
            (cyclicPowerHom (k : G) hk c) =
          carryPhase ζ hζ (1 : ZMod 3) a b c * twoCoboundary β a b c)
    {W : Type*} [AddCommGroup W] [Module ℂ W] (L_W : Module.End ℂ W)
    [FiniteDimensional ℂ (L_W.eigenspace (2 : ℂ))]
    (vacuumInclusion : fixedStates(U, K) →ₗ[ℂ] W)
    (hVacuumInjective : Function.Injective vacuumInclusion)
    (hVacuumWeight : ∀ x : fixedStates(U, K), (x : Carrier D) ∈ grade D 2 →
      vacuumInclusion x ∈ L_W.eigenspace (2 : ℂ)) :
    2 ≤ Module.finrank ℂ (L_W.eigenspace (2 : ℂ)) := by
  have hRealization : Function.Injective charge.toAdditiveLeft :=
    Multiplicative.toAdd.injective.comp (hCharge.comp Additive.toMul.injective)
  have hRealizationExhaustive (t : AddAut (Charge D))
      (ht : ∀ a b, bilinear D (t a) (t b) = bilinear D a b) :
      ∃ g : Additive A, charge.toAdditiveLeft g = t := by
    obtain ⟨g, hg⟩ := hExhaustive t ht
    exact ⟨Additive.ofMul g, hg⟩
  obtain ⟨π, η, hTransport⟩ := conformal_ground_projection D hPos hRoot inverse hInverse
    charge.toAdditiveLeft hRealization hRealizationExhaustive (U.comp K.subtype)
    (fun k u n v => hMode k u v n) hOmega
  have hGround (k : K) (a : Charge D) :
      U k (ground D a) = (η k a : ℂ) • ground D ((charge (π k)).toAdd a) :=
    hTransport k a
  refine p48p_associator_extension_obstruction_of_derived_action D hRank hPos N L hNL
    hCard hIndex φ hφ charge hCharge hIsometry ρ hρ s hs hsImage hsCentral c hc hcCentral
    hcOutside hAllowed hFixedEleven hFixedTwentyThree π.range K π.rangeRestrict
    π.rangeRestrict_surjective U hU η hMode hGround α γ hRestricted ζ hζ ?_
    L_W vacuumInclusion hVacuumInjective hVacuumWeight
  intro k hk hOrder hFixedRank hStandard
  exact hType k hk (π k) (η k) hOrder hFixedRank (hGround k) hStandard

#print axioms p48p_associator_extension_obstruction_of_conformal_action

end D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.P48pConformalExtension
