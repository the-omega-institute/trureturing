/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pDerivedExtension
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/CubicObstruction/P48pDerivedExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full P48p derived action supplies the projected data for the extension obstruction. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.P48pDerivedAction
import D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.P48pExtension
import Mathlib.GroupTheory.Index
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.P48pDerivedExtension

open Automorphisms.ReducibleActionWeightTwo (realChargeRepresentation)
open DiagonalCharacterConjugacy (PreservesModes ground)
open FiniteGroups.Cyclic.CyclicAssociatorObstruction (carryPhase cyclicPowerHom twoCoboundary)
open LatticeGeneratingFieldLocality (LatticeData Carrier Charge bilinear)
open LatticePositiveEnergy (grade)
open P48pDerivedAction (p48p_derived_action_charge_inversion_and_cubic_rank)
open P48pExtension (p48p_associator_extension_obstruction)

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 23)
local notation "fixedCartan(" D ", " charge ", " g ")" =>
  LinearMap.ker (realChargeRepresentation D (charge g) - 1)
local notation "fixedStates(" U ", " K ")" =>
  Representation.invariants
    (MonoidHom.comp (MonoidHom.comp LinearEquiv.automorphismGroup.toLinearMapMonoidHom U)
      (Subgroup.subtype K))

/-- The P48p derived action on the full charge group supplies the inversion
and cubic rank needed for the extension obstruction on any projected subgroup. -/
theorem p48p_associator_extension_obstruction_of_derived_action
    (D : LatticeData) (hRank : D.rank = 48)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    {A : Type*} [Group A] [Finite A] (N L : Subgroup A) [N.Normal] (hNL : N ≤ L)
    (hCard : Nat.card N ∣ 2 ^ 4 * 3 * 11 * 23) (hIndex : N.index ∣ 12)
    (φ : N →* SL23) (hφ : Function.Injective φ)
    (charge : A →* Multiplicative (AddAut (Charge D))) (hCharge : Function.Injective charge)
    (hIsometry : ∀ g : A, ∀ a b,
      bilinear D ((charge g).toAdd a) ((charge g).toAdd b) = bilinear D a b)
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
    (H : Subgroup A) {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    (π : K →* H) (hπ : Function.Surjective π)
    (U : G →* (Carrier D ≃ₗ[ℂ] Carrier D)) (hU : Function.Injective U)
    (phase : K → Charge D → ℂˣ) (hMode : ∀ k : K, PreservesModes D (U k))
    (hGround : ∀ (k : K) a,
      U k (ground D a) = (phase k a : ℂ) • ground D ((charge (π k : A)).toAdd a))
    (α : G → G → G → ℂˣ) (γ : K → K → ℂˣ)
    (hRestricted : ∀ a b c : K, α a.val b.val c.val = twoCoboundary γ a b c)
    (ζ : ℂˣ) (hζ : orderOf ζ = 3)
    (hType : ∀ (k : K) (hk : orderOf (k : G) = 3), orderOf (charge (π k : A)) = 3 →
      Module.finrank ℝ (fixedCartan(D, charge, (π k : A))) = 16 →
      (∀ a, (charge (π k : A)).toAdd a = a → phase k a = 1) →
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
  obtain ⟨hNeg, hDerivedCubic⟩ :=
    p48p_derived_action_charge_inversion_and_cubic_rank D hRank N L hNL φ hφ charge hCharge
      ρ hρ s hs hsImage hsCentral c hc hcCentral hcOutside hAllowed
  let M := N.comap H.subtype
  letI : M.Normal := (inferInstance : (N.comap H.subtype).Normal)
  have hMIndex : M.index ∣ 12 := (N.relIndex_dvd_index_of_normal H).trans hIndex
  have hMCard : Nat.card M ∣ 2 ^ 4 * 3 * 11 * 23 :=
    (N.card_comap_dvd_of_injective H.subtype H.subtype_injective).trans hCard
  let toN : M →* N := (H.subtype.comp M.subtype).codRestrict N fun m => m.property
  have hToN : Function.Injective toN :=
    ((H.subtype.comp M.subtype).injective_codRestrict N _).2
      (H.subtype_injective.comp M.subtype_injective)
  have hOrder (m : M) : orderOf (toN m) = orderOf m := orderOf_injective toN hToN m
  let chargeH := charge.comp H.subtype
  have hCubic (m : M) (hm : orderOf m = 3) :
      Module.finrank ℝ (fixedCartan(D, chargeH, (m : H))) = 16 ∧
      fixedCartan(D, chargeH, (m : H)) ≠ ⊥ ∧ fixedCartan(D, chargeH, (m : H)) ≠ ⊤ :=
    (hDerivedCubic (toN m) ((hOrder m).trans hm)
      (Subgroup.inclusion hNL (toN m)) (Set.mem_insert _ _)).2
  have hDim : Module.finrank ℝ (Fin D.rank → ℝ) = 48 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hRank]
  have properFixedSpace (m : M) (r : ℕ)
      (hr : Module.finrank ℝ (fixedCartan(D, chargeH, (m : H))) = r)
      (hNonzero : r ≠ 0) (hProper : r ≠ 48) :
      fixedCartan(D, chargeH, (m : H)) ≠ ⊥ ∧ fixedCartan(D, chargeH, (m : H)) ≠ ⊤ := by
    constructor
    · intro h
      rw [h, finrank_bot] at hr
      exact hNonzero hr.symm
    · intro h
      rw [h, finrank_top, hDim] at hr
      exact hProper hr.symm
  refine p48p_associator_extension_obstruction D hRank hPos M hMCard hMIndex
    (φ.comp toN) (hφ.comp hToN) chargeH (hCharge.comp H.subtype_injective)
    (fun g => hIsometry (g : A)) ?_ ?_ (fun m hm => (hCubic m hm).1)
    K π hπ U hU phase hMode hGround α γ hRestricted ζ hζ hType L_W
    vacuumInclusion hVacuumInjective hVacuumWeight
  · intro m hm
    exact hNeg (toN m) hm
  · intro m hm
    rcases hm with hm | hm | hm
    · exact (hCubic m hm).2
    · exact properFixedSpace m 8 (hFixedEleven (toN m) ((hOrder m).trans hm))
        (by decide) (by decide)
    · exact properFixedSpace m 4 (hFixedTwentyThree (toN m) ((hOrder m).trans hm))
        (by decide) (by decide)

#print axioms p48p_associator_extension_obstruction_of_derived_action

end D5.S3.VertexAlgebra.Lattice.Orbifold.CubicObstruction.P48pDerivedExtension
