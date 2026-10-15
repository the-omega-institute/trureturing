import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseBounds
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseBounds

open _root_.D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseBounds
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
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => l1Deviation p.1 p.2 z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ x y z, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
    z ∈ Set.Icc (0 : ℝ) 1 → r.readout () ⟨x, y⟩ z ≤
      2 * ((1 - x) + (1 - y) + (1 - z))

theorem actual_law : arena.Law actual := ejm_noise_l1_bound

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh

set_option maxRecDepth 10000 in
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
    change l1Deviation 1 1 0 = l1Deviation 1 1 1 at h
    simp only [l1Deviation, ejm_noise_probability, Fin.sum_univ_four, ejmNoiseTable] at h
    norm_num only [Fin.ext_iff, Fin.coe_ofNat_eq_mod, Fin.val_mk,
      and_true, and_false, true_and, false_and] at h
    norm_num [ite_true, ite_false] at h

def four_slot_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseBounds.ejm_noise_l1_bound)
    (type_of% actual) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseBounds.ejm_noise_l1_bound.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseBounds.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => l1Deviation p.1 p.2 z)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseBounds
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
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

end Reg.D5.S3.Quantum.Entanglement.ElegantJointMeasurementNoiseBounds
