import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation
open LeanInformationAudit
open scoped Matrix.Norms.L2Operator

namespace Reg.D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation

abbrev signature : Signature where
  Params := ℝ → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ f x => f x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : Type} [Fintype n] [DecidableEq n]
    (f : ℝ → ℝ) (a b : ℝ) (H : Matrix n n ℂ)
    (hH : IsSelfAdjoint H) (hHH : H * H = 1),
    cfc f (a • (1 : Matrix n n ℂ) + b • H) =
      ((R.readout () f (a + b) + f (a - b)) / 2) • (1 : Matrix n n ℂ) +
      ((f (a + b) - f (a - b)) / 2) • H

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hH : IsSelfAdjoint (1 : Matrix Unit Unit ℂ) := IsSelfAdjoint.one _
  have hHH : (1 : Matrix Unit Unit ℂ) * 1 = 1 := by simp
  have bad := h (fun _ => 1) 0 0 (1 : Matrix Unit Unit ℂ) hH hHH
  have good := two_point_cfc (fun _ => 1) 0 0 (1 : Matrix Unit Unit ℂ) hH hHH
  have contradiction := congrArg (fun M : Matrix Unit Unit ℂ => (M () ()).re)
    (good.symm.trans bad)
  norm_num [rejected, realize, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Complex.smul_re, smul_eq_mul] at contradiction

def registration : Registration arena (type_of% (@two_point_cfc)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@two_point_cfc, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨id, 0, 1, ?_⟩
    norm_num [actual, realize]

noncomputable def registration_1 :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation.two_point_cfc)
      (type_of% (realize signature
        (fun _ f x => f x) (fun e => nomatch e))) Unit Unit := {
  unitName :=
    `D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation.two_point_cfc.__information_unit
  realizationName :=
    `Reg.D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ f x => f x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration
#print axioms registration_1
#print axioms _root_.D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation.two_point_cfc

end Reg.D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation
