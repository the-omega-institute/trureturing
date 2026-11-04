import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition
import Reg.Support.DependentFamily

/-! Registration of the full complex spectral-channel identity. -/

namespace Reg.D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition

open _root_.D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ComplexConjugate

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The second spectral sample varies over the full complex plane. -/
abbrev signature : Signature where
  Params := ℂ
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ second => second) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ first second : ℂ,
    Complex.normSq (evenSpectralChannel first second) -
        Complex.normSq (oddSpectralChannel first second) =
      (first * conj (r.readout () first second)).re

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have atOne := h 1 1
  norm_num [rejected, realize, evenSpectralChannel, oddSpectralChannel] at atOne

def source_registration : Registration arena (type_of% @channel_energy_difference) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨channel_energy_difference, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    exact zero_ne_one

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@channel_energy_difference) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition.unit
  realizationName := `Reg.D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ second => second) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end

end Reg.D5.S3.Weil.HolonomyBridge.OffLineOrbitParityDecomposition
