import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldMoonshineCharacter

/-! Register the value of the actual moonshine character at an upper-half-plane point. -/

set_option autoImplicit false

noncomputable section

open Filter LeanInformationAudit UpperHalfPlane
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.OriginalOrbifoldAnalyticCharacter (character)
open _root_.D5.S3.VertexAlgebra.OriginalOrbifoldCuspExpansion (weightedCharacter_tendsto)
open _root_.D5.S3.VertexAlgebra.OriginalOrbifoldMoonshineCharacter
  (character_eq_eisensteinCube_div_discriminant_sub_744)
open ModularForm (E₄ discriminant)

namespace Reg.D5.S3.VertexAlgebra.Characters.OriginalOrbifoldMoonshineCharacter

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℍ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ τ => character τ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law a := ∀ τ : ℍ, a.readout () () τ = E₄ τ ^ (3 : ℕ) / discriminant τ - 744

private theorem character_not_constant (c : ℂ) : ¬ ∀ τ : ℍ, character τ = c := by
  intro hc
  have hΔ : Tendsto discriminant atImInfty (𝓝 (0 : ℂ)) :=
    ModularForm.discriminant_isZeroAtImInfty
  have hz : Tendsto (fun τ : ℍ => c * discriminant τ) atImInfty (𝓝 (0 : ℂ)) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := c)).mul hΔ
  have hχΔ : Tendsto (fun τ : ℍ => character τ * discriminant τ) atImInfty (𝓝 (0 : ℂ)) :=
    hz.congr (fun τ => by rw [hc τ])
  exact zero_ne_one (tendsto_nhds_unique hχΔ weightedCharacter_tendsto)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply character_not_constant 0
  intro τ
  exact (character_eq_eisensteinCube_div_discriminant_sub_744 τ).trans (h τ).symm

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨τ, hτ⟩ := not_forall.mp (character_not_constant (character UpperHalfPlane.I))
  exact ⟨(), τ, UpperHalfPlane.I, hτ⟩

def family : Registration arena
    (type_of% (@character_eq_eisensteinCube_div_discriminant_sub_744)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨character_eq_eisensteinCube_div_discriminant_sub_744, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@character_eq_eisensteinCube_div_discriminant_sub_744) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Characters.OriginalOrbifoldMoonshineCharacter.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Characters.OriginalOrbifoldMoonshineCharacter.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ τ => character τ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.OriginalOrbifoldMoonshineCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.VertexAlgebra.Characters.OriginalOrbifoldMoonshineCharacter
