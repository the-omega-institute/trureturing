import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Divergence.CoherenceL1RelativeEntropyBound
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of Hermitian and unitary reflections. -/

namespace Reg.D5.S3.Divergence.CoherenceL1RelativeEntropyBound

open _root_.D5.S3.Divergence.CoherenceL1RelativeEntropyBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the reflection of a matrix at every dimension, including zero. -/
abbrev signature : Signature where
  Params := ℕ
  State n := Matrix (Fin n) (Fin n) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin n) (Fin n) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ P => reflection P) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (0 : Matrix (Fin 1) (Fin 1) ℂ), (1 : Matrix (Fin 1) (Fin 1) ℂ), ?_⟩
  intro he
  have hc := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) he
  norm_num [actual, realize, reflection, Matrix.one_apply] at hc

namespace Hermitian

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => Complex.I) (fun e => nomatch e)

/-- Retain the Hermitian hypothesis and the complete Hermitian conclusion. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (_hP : P.IsHermitian),
    (R.readout () n P).IsHermitian

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (n := 1) 0 Matrix.isHermitian_zero).apply 0 0
  have hi := congrArg Complex.im he
  norm_num [rejected, realize] at hi

def source_registration : Registration arena (type_of% @reflection_hermitian) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reflection_hermitian, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@reflection_hermitian) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Divergence.CoherenceL1RelativeEntropyBound.Hermitian.unit
  realizationName :=
    `Reg.D5.S3.Divergence.CoherenceL1RelativeEntropyBound.Hermitian.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P => reflection P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Divergence.CoherenceL1RelativeEntropyBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Hermitian

namespace Unitary

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain both projection hypotheses and the complete unitary conclusion. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (_hP : P.IsHermitian) (_hPP : P * P = P),
    R.readout () n P ∈ Matrix.unitaryGroup (Fin n) ℂ

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := Matrix.mem_unitaryGroup_iff.mp
    (h (n := 1) 0 Matrix.isHermitian_zero (by simp))
  change (0 : Matrix (Fin 1) (Fin 1) ℂ) * star 0 = 1 at hz
  have he := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) hz
  simp at he

def source_registration : Registration arena (type_of% @reflection_unitary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reflection_unitary, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@reflection_unitary) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Divergence.CoherenceL1RelativeEntropyBound.Unitary.unit
  realizationName :=
    `Reg.D5.S3.Divergence.CoherenceL1RelativeEntropyBound.Unitary.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ P => reflection P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Divergence.CoherenceL1RelativeEntropyBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Unitary

end
end Reg.D5.S3.Divergence.CoherenceL1RelativeEntropyBound
