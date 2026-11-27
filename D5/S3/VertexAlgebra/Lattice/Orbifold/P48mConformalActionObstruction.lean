/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48mConformalActionObstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48mConformalActionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual conformal actions with the P48m isometry data force two fixed weight-two states. -/

import D5.S3.VertexAlgebra.Lattice.Automorphisms.ConformalGroundTransport
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48mNormalizerObstruction
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSplitActionObstruction
import OmegaBuild.Commands

/-!
The order and fixed-rank inputs have the sources recorded in
`P48mNormalizerObstruction`. The charge projection of an actual conformal
action induces its action on rational currents. A linear inclusion of the
fixed states intertwining the actual Sugawara zero mode preserves weight two.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48mConformalActionObstruction

open LatticeGeneratingFieldLocality (LatticeData Charge Carrier bilinear)
open LatticeAllStateField (Y)
open LatticeActualConformalState (omega omega_modes)
open LatticePositiveEnergy (grade actualL0_eigen_iff_grade)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open Lattice.Automorphisms.ConformalGroundTransport (conformal_ground_projection)
open DiagonalCharacterConjugacy (PreservesModes ground)
open P48mNormalizerObstruction (p48m_fixed_weight_two)
open P48qInvariantQuadratics (RationalCartan rationalGram rationalCurrent)
open scoped Matrix VertexOperator

open private rationalAction rationalExtension_preserves_gram rationalCurrent_lift from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSplitActionObstruction

private noncomputable def fixedL0 (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    {E : Type*} [Group E] (U : E →* (Carrier D ≃ₗ[ℂ] Carrier D))
    (hMode : ∀ e, PreservesModes D (U e))
    (hOmega : ∀ e, U e (omega D H) = omega D H) :
    Module.End ℂ (Representation.invariants
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp U)) := by
  refine (sugawaraMode D H 0).restrict ?_
  intro v hv
  apply (Representation.mem_invariants _ _).mpr
  intro e
  have hFixed : U e v = v := (Representation.mem_invariants _ v).mp hv e
  change U e (sugawaraMode D H 0 v) = sugawaraMode D H 0 v
  have hL0 : ((Y D (omega D H))[[1]]) = sugawaraMode D H 0 := by
    simpa using omega_modes D H 0
  have he := hMode e (omega D H) v 1
  rw [hOmega e, hL0, hFixed] at he
  exact he

/-- The P48m group and fixed-rank data give two independent actual fixed
weight-two states for any conformal action. An injective inclusion
intertwining the actual conformal zero mode carries both into the target
weight-two eigenspace. -/
theorem p48m_conformal_action_obstruction (D : LatticeData) (hRank : D.rank = 48)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hRoot : ∀ a : Charge D, bilinear D a a ≠ 2)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    {G E : Type*} [Group G] [Group E]
    (realization : Additive G →+ AddAut (Charge D))
    (hFaithful : Function.Injective realization)
    (hIsometry : ∀ g : Additive G, ∀ a b,
      bilinear D (realization g a) (realization g b) = bilinear D a b)
    (hExhaustive : ∀ t : AddAut (Charge D),
      (∀ a b, bilinear D (t a) (t b) = bilinear D a b) → ∃ g, realization g = t)
    (s : G) (hGroupOrder : Nat.card G = 1200)
    (hNormalizerOrder : Nat.card (Subgroup.normalizer (Subgroup.zpowers s : Set G)) = 1200)
    (hFixedRank : Module.finrank ℚ (Representation.invariants
      (((rationalAction D).comp realization.toMultiplicativeRight).comp
        (Subgroup.zpowers s).subtype)) = 16)
    (U : E →* (Carrier D ≃ₗ[ℂ] Carrier D))
    (hMode : ∀ e, PreservesModes D (U e))
    (hOmega : ∀ e, U e (omega D H) = omega D H)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V)
    [FiniteDimensional ℂ (L.eigenspace (2 : ℂ))] :
    let A : Representation ℂ E (Carrier D) :=
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp U
    ∀ (inclusion : A.invariants →ₗ[ℂ] V), Function.Injective inclusion →
      (∀ x, L (inclusion x) = inclusion (fixedL0 D H U hMode hOmega x)) →
      ∃ (π : E →* G) (phase : E → Charge D → ℂˣ),
        (∀ e a, U e (ground D a) =
          (phase e a : ℂ) • ground D (realization (Additive.ofMul (π e)) a)) ∧
        (∀ e x, U e (rationalCurrent D x) = rationalCurrent D
          (((rationalAction D).comp realization.toMultiplicativeRight) (π e) x)) ∧
        (∃ q : Fin 2 → Carrier D,
          (∀ i, q i ∈ grade D 2) ∧ (∀ e i, U e (q i) = q i) ∧ LinearIndependent ℂ q) ∧
        2 ≤ Module.finrank ℂ (L.eigenspace (2 : ℂ)) := by
  intro A inclusion hInjective hIntertwine
  obtain ⟨π, phase, hGround⟩ := conformal_ground_projection D hPos hRoot H hHG
    realization hFaithful hExhaustive U (fun e a n b => hMode e a b n) hOmega
  let ρ : Representation ℚ G (RationalCartan D) :=
    (rationalAction D).comp realization.toMultiplicativeRight
  have hGram (g : G) (x y : RationalCartan D) :
      rationalGram D (ρ g x) (ρ g y) = rationalGram D x y :=
    rationalExtension_preserves_gram D _ (hIsometry (Additive.ofMul g)) x y
  have hCurrent (e : E) (x : RationalCartan D) :
      U e (rationalCurrent D x) = rationalCurrent D (ρ (π e) x) :=
    rationalCurrent_lift D _ (hIsometry (Additive.ofMul (π e)))
      (U e) (phase e) (hMode e) (hGround e) x
  obtain ⟨q, hGrade, hFixed, hIndependent⟩ := p48m_fixed_weight_two D hRank hPos ρ π A
    hGram hCurrent (fun e a n b => hMode e a b n) s hGroupOrder hNormalizerOrder hFixedRank
  have hWeight (x : A.invariants) (hx : (x : Carrier D) ∈ grade D 2) :
      inclusion x ∈ L.eigenspace (2 : ℂ) := by
    have hEigen : fixedL0 D H U hMode hOmega x = (2 : ℂ) • x := by
      apply Subtype.ext
      change sugawaraMode D H 0 (x : Carrier D) = (2 : ℂ) • (x : Carrier D)
      simpa only [Int.cast_ofNat] using
        (actualL0_eigen_iff_grade D H hHG (mul_eq_one_comm.mp hHG) 2 (x : Carrier D)).mpr hx
    apply Module.End.mem_eigenspace_iff.mpr
    rw [hIntertwine x, hEigen, map_smul]
  let qFixed (i : Fin 2) : A.invariants := ⟨q i, fun e => hFixed e i⟩
  have hFixedIndependent : LinearIndependent ℂ qFixed :=
    LinearIndependent.of_comp A.invariants.subtype hIndependent
  let qImage (i : Fin 2) : L.eigenspace (2 : ℂ) :=
    ⟨inclusion (qFixed i), hWeight (qFixed i) (hGrade i)⟩
  have hImageIndependent : LinearIndependent ℂ qImage := by
    apply LinearIndependent.of_comp (L.eigenspace (2 : ℂ)).subtype
    exact hFixedIndependent.map' inclusion (LinearMap.ker_eq_bot.mpr hInjective)
  refine ⟨π, phase, hGround, hCurrent, ⟨q, hGrade, hFixed, hIndependent⟩, ?_⟩
  simpa only [Fintype.card_fin] using hImageIndependent.fintype_card_le_finrank

run_cmd do
  let name := ``p48m_conformal_action_obstruction
  let axioms ← Lean.collectAxioms name
  unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
    throwError "Unexpected axiom closure for {name}: {axioms}"
  Lean.logInfo m!"{name} depends on axioms: {axioms}"

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48mConformalActionObstruction
