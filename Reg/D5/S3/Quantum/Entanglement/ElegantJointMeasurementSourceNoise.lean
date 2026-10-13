import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise

open _root_.D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option backward.isDefEq.respectTransparency false

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 4 → Fin 4 → Fin 4 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => ejmProbability p.1 p.2 z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ x y z a b c, r.readout () ⟨x, y⟩ z a b c = ejmNoiseTable x y z a b c

theorem actual_law : arena.Law actual := ejm_noise_probability

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 0 0 0 0
  norm_num [rejected, realize, ejmNoiseTable] at hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      have hji : j = i := Subsingleton.elim (α := Unit) j i
      exact (h hji).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨(1 : ℝ), (1 : ℝ)⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    intro h
    have hh := congrArg (fun p => p 0 0 0) h
    change ejmProbability 1 1 0 0 0 0 = ejmProbability 1 1 1 0 0 0 at hh
    rw [ejm_noise_probability, ejm_noise_probability] at hh
    norm_num [ejmNoiseTable] at hh

def four_slot_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise.ejm_noise_probability)
    (type_of% actual) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise.ejm_noise_probability.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => ejmProbability p.1 p.2 z)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms four_slot_registration

end

end Reg.D5.S3.Quantum.Entanglement.ElegantJointMeasurementSourceNoise
