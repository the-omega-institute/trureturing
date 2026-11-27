/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pExtension
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A type-one ambient associator forces two weight-two states in a P48p extension. -/

import D5.S3.FiniteGroups.Cyclic.CyclicAssociatorObstruction
import D5.S3.FiniteGroups.Cyclic.P48pCartanDichotomy
import D5.S3.VertexAlgebra.Lattice.Automorphisms.ReducibleActionWeightTwo
import D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.StandardCubicOfProjectedInversion
import OmegaBuild.Commands

/-!
The projected normal-factor and fixed-rank hypotheses encode the P48p lattice
input from Nebe, arXiv:1212.0865, Theorem 3.6, proof (B), and Proposition 4.8.
The type comparison includes the identification of the actual twisted spectrum
and ambient cyclic associator with the type-one carry class in the convention
of Evans–Gannon, arXiv:1804.11145, equations (2.13) and (2.14).
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.P48pExtension

open Automorphisms.ReducibleActionWeightTwo
  (realChargeAction realChargeRepresentation reducible_action_fixed_weight_two)
open DiagonalCharacterConjugacy (PreservesModes ground)
open FiniteGroups.Cyclic.CyclicAssociatorObstruction
  (carryPhase cyclicPowerHom not_mem_of_nonzero_type twoCoboundary)
open LatticeActualConformalState (omega)
open LatticeGeneratingFieldLocality (LatticeData Carrier Charge bilinear)
open LatticePositiveEnergy (grade)
open StandardCubicOfProjectedInversion (standard_cubic_of_projected_inversion)

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 23)
local notation "fixedCartan(" D ", " charge ", " h ")" =>
  LinearMap.ker (realChargeRepresentation D (charge h) - 1)
local notation "fixedStates(" U ", " K ")" =>
  Representation.invariants
    (MonoidHom.comp (MonoidHom.comp LinearEquiv.automorphismGroup.toLinearMapMonoidHom U)
      (Subgroup.subtype K))

/-- A rank-48 lattice action with the P48p projected group and rank data
forces target weight-two dimension at least two. The actual subgroup projects
onto the charge group and trivializes the ambient associator. The external type
comparison identifies its standard rank-sixteen cubic lifts with the type-one
carry representative up to an explicit two-coboundary. -/
theorem p48p_associator_extension_obstruction
    (D : LatticeData) (hRank : D.rank = 48)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hCard : Nat.card N ∣ 2 ^ 4 * 3 * 11 * 23) (hIndex : N.index ∣ 12)
    (φ : N →* SL23) (hφ : Function.Injective φ)
    (charge : H →* Multiplicative (AddAut (Charge D)))
    (hCharge : Function.Injective charge)
    (hIsometry : ∀ h : H, ∀ a b,
      bilinear D ((charge h).toAdd a) ((charge h).toAdd b) = bilinear D a b)
    (hNeg : ∀ n : N, φ n = -(1 : SL23) → ∀ a, (charge (n : H)).toAdd a = -a)
    (hFix : ∀ n : N, (orderOf n = 3 ∨ orderOf n = 11 ∨ orderOf n = 23) →
      fixedCartan(D, charge, (n : H)) ≠ ⊥ ∧ fixedCartan(D, charge, (n : H)) ≠ ⊤)
    (hCubic : ∀ n : N, orderOf n = 3 →
      Module.finrank ℝ (fixedCartan(D, charge, (n : H))) = 16)
    {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (π : K →* H) (hπ : Function.Surjective π)
    (U : G →* (Carrier D ≃ₗ[ℂ] Carrier D)) (hU : Function.Injective U)
    (phase : K → Charge D → ℂˣ) (hMode : ∀ k : K, PreservesModes D (U k))
    (hGround : ∀ (k : K) a,
      U k (ground D a) = (phase k a : ℂ) • ground D ((charge (π k)).toAdd a))
    (α : G → G → G → ℂˣ) (γ : K → K → ℂˣ)
    (hRestricted : ∀ a b c : K, α a.val b.val c.val = twoCoboundary γ a b c)
    (ζ : ℂˣ) (hζ : orderOf ζ = 3)
    (hType : ∀ (k : K) (hk : orderOf (k : G) = 3), orderOf (charge (π k)) = 3 →
      Module.finrank ℝ (fixedCartan(D, charge, π k)) = 16 →
      (∀ a, (charge (π k)).toAdd a = a → phase k a = 1) →
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
  let ρ := (realChargeRepresentation D).comp charge
  have hDim : Module.finrank ℝ (Fin D.rank → ℝ) = 48 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hRank]
  rcases ExtremalC48.p48p_real_cartan_dichotomy N ρ hDim hCard hIndex φ hφ hFix hCubic with
    ⟨S, hBot, hTop, hStable⟩ | ⟨hNegOne, n, hn, hRankN⟩
  · have hInvariant (k : K) (v : Fin D.rank → ℝ) (hv : v ∈ S) :
        realChargeAction D (charge (π k)).toAdd v ∈ S := hStable (π k) hv
    obtain ⟨C, P, _, hGrade, _, hFixed, hIndependent⟩ :=
      reducible_action_fixed_weight_two D hPos (fun k => (charge (π k)).toAdd)
        (fun k => hIsometry (π k)) (fun k => U k) phase hMode hGround S hBot hTop hInvariant
    let q : Fin 2 → Carrier D := ![omega D (P * C), omega D C]
    let qFixed (i : Fin 2) : fixedStates(U, K) := ⟨q i, fun k => hFixed k i⟩
    have hFixedIndependent : LinearIndependent ℂ qFixed :=
      LinearIndependent.of_comp fixedStates(U, K).subtype hIndependent
    let qImage (i : Fin 2) : L_W.eigenspace (2 : ℂ) :=
      ⟨vacuumInclusion (qFixed i), hVacuumWeight (qFixed i) (hGrade i)⟩
    have hImageIndependent : LinearIndependent ℂ qImage :=
      LinearIndependent.of_comp (L_W.eigenspace (2 : ℂ)).subtype
        (hFixedIndependent.map' vacuumInclusion (LinearMap.ker_eq_bot.mpr hVacuumInjective))
    simpa only [Fintype.card_fin] using hImageIndependent.fintype_card_le_finrank
  · obtain ⟨m, hm⟩ := hNegOne
    obtain ⟨x, hx⟩ := hπ (n : H)
    obtain ⟨s, hs⟩ := hπ (m : H)
    have hxCharge : orderOf (charge (π x)) = 3 := by
      rw [hx, orderOf_injective charge hCharge]
      exact (orderOf_injective N.subtype Subtype.val_injective n).trans hn
    have hsNeg (a : Charge D) : (charge (π s)).toAdd a = -a := by
      rw [hs]
      exact hNeg m hm a
    let z : K := (x * (s * x * s⁻¹)) ^ 2
    obtain ⟨hzCharge, hzOrder, hzPhase⟩ :=
      standard_cubic_of_projected_inversion D (U.comp K.subtype) (charge.comp π) phase
        (hU.comp Subtype.val_injective) hMode hGround x s hxCharge hsNeg (hIsometry (π x))
    change charge (π z) = charge (π x) at hzCharge
    change orderOf z = 3 at hzOrder
    change ∀ a, (charge (π x)).toAdd a = a → phase z a = 1 at hzPhase
    have hzProjected : π z = (n : H) := (hCharge hzCharge).trans hx
    have hzRank : Module.finrank ℝ (fixedCartan(D, charge, π z)) = 16 := by
      rw [hzProjected]
      exact hRankN
    have hzAmbient : orderOf (z : G) = 3 :=
      (orderOf_injective K.subtype Subtype.val_injective z).trans hzOrder
    have hzFixed (a : Charge D) (ha : (charge (π z)).toAdd a = a) : phase z a = 1 :=
      hzPhase a (by rwa [← hzCharge])
    have hzChargeOrder : orderOf (charge (π z)) = 3 := by rwa [hzCharge]
    obtain ⟨β, hCompare⟩ := hType z hzAmbient hzChargeOrder hzRank hzFixed
    have hzExcluded := not_mem_of_nonzero_type (by decide) α (z : G) hzAmbient ζ hζ
      (1 : ZMod 3) (by decide) β hCompare
    exact (hzExcluded K γ hRestricted z.property).elim

#print axioms p48p_associator_extension_obstruction

end D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.P48pExtension
