/- GID: D5/S3/VertexAlgebra/Lattice/Automorphisms/P48pSmallFactorFixedWeightTwo
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Automorphisms/P48pSmallFactorFixedWeightTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The small P48p charge subgroup gives two independent actual fixed weight-two states. -/

import D5.S3.FiniteGroups.Cyclic.RealIrreducibleDegreeBound
import D5.S3.VertexAlgebra.Lattice.Automorphisms.ReducibleActionWeightTwo

/-! Apply real Cartan reducibility to the small normal-factor branch of P48p. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Automorphisms.P48pSmallFactorFixedWeightTwo

open LatticeGeneratingFieldLocality (LatticeData Charge Carrier bilinear)
open LatticeAllStateField (Y)
open LatticeActualConformalState (omega)
open LatticePositiveEnergy (grade)
open LatticeSugawaraCurrents (gramComplex)
open Lattice.Orbifold.DiagonalCharacterConjugacy (PreservesModes ground)
open ReducibleActionWeightTwo
  (realChargeRepresentation realChargeAction reducible_action_fixed_weight_two)
open scoped VertexOperator

/-- A rank-48 actual action projecting to a charge group with the small P48p
factor bounds fixes two independent states of actual conformal weight two.
The action can include a kernel on the charge group, and the ground phases can
vary with the group element and charge. -/
theorem p48p_small_factor_fixed_weight_two (D : LatticeData) (hRank : D.rank = 48)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    {H E : Type*} [Group H] [Finite H] [Group E]
    (K : Subgroup H) (hSmall : Nat.card K ≤ 16) (hIndex : K.index ∣ 12)
    (charge : H →* Multiplicative (AddAut (Charge D)))
    (hIsometry : ∀ h : H, ∀ a b, bilinear D ((charge h).toAdd a) ((charge h).toAdd b) =
      bilinear D a b)
    (π : E →* H) (U : E →* (Carrier D ≃ₗ[ℂ] Carrier D)) (phase : E → Charge D → ℂˣ)
    (hMode : ∀ e, PreservesModes D (U e))
    (hGround : ∀ e a, U e (ground D a) =
      (phase e a : ℂ) • ground D ((charge (π e)).toAdd a)) :
    ∃ C : Matrix (Fin D.rank) (Fin D.rank) ℂ, C * gramComplex D = 1 ∧
      ∃ q : Fin 2 → Carrier D,
        (∀ i, q i ∈ grade D 2) ∧
        (∀ i, ((Y D (omega D C))[[1]]) (q i) = (2 : ℂ) • q i) ∧
        (∀ e i, U e (q i) = q i) ∧ LinearIndependent ℂ q := by
  let ρ : Representation ℝ H (Fin D.rank → ℝ) := (realChargeRepresentation D).comp charge
  have hDim : Module.finrank ℝ (Fin D.rank → ℝ) = 48 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hRank]
  obtain ⟨W, hBot, hTop, hW⟩ :=
    ExtremalC48.p48p_small_factor_exists_real_invariant_subspace K ρ hDim hSmall hIndex
  have hInvariant (e : E) (x : Fin D.rank → ℝ) (hx : x ∈ W) :
      realChargeAction D (charge (π e)).toAdd x ∈ W := hW (π e) hx
  obtain ⟨C, P, hCG, hStates⟩ :=
    reducible_action_fixed_weight_two D hPos (fun e => (charge (π e)).toAdd)
      (fun e => hIsometry (π e)) (fun e => U e) phase hMode hGround W hBot hTop hInvariant
  exact ⟨C, hCG, ![omega D (P * C), omega D C], hStates⟩

#print axioms p48p_small_factor_fixed_weight_two

end D5.S3.VertexAlgebra.Lattice.Automorphisms.P48pSmallFactorFixedWeightTwo
