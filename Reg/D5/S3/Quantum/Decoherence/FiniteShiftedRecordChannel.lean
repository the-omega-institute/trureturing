import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel
import Reg.Support.SingleDependentReadout

/-! Four-slot registration for finite diagonal Kraus completeness. -/

open D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel

noncomputable section
universe u_1 u_2

abbrev signature : Signature.{max (u_1 + 1) (u_2 + 1), u_1, 0, 0, 0} where
  Params := Σ ι : Type u_1, Σ ε : Type u_2, Σ record : ι → ε → ℂ, ε
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def witnessReadout : ∀ (_ : Unit) (p : signature.{u_1, u_2}.Params),
    signature.State p → ℂ :=
  fun _ p i => p.2.2.1 i p.2.2.2

def witnessAnchor : ∀ (_ : Empty) (p : signature.{u_1, u_2}.Params),
    signature.State p :=
  fun e _ => Empty.elim e

def actual : Realization signature.{u_1, u_2} :=
  realize signature.{u_1, u_2} (fun _ p i => p.2.2.1 i p.2.2.2)
    (fun e _ => Empty.elim e)

def rejected : Realization signature.{u_1, u_2} :=
  realize signature.{u_1, u_2} (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena.{max (u_1 + 1) (u_2 + 1), u_1, 0, 0, 0} where
  signature := signature.{u_1, u_2}
  Law R := ∀ {ι : Type u_1} {ε : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype ε]
    (record : ι → ε → ℂ)
    (hnorm : ∀ i, ∑ a, ‖record i a‖ ^ 2 = (1 : ℝ)),
    (∑ a : ε, ((Matrix.diagonal (fun i =>
      R.readout () ⟨ι, ⟨ε, ⟨record, a⟩⟩⟩ i)).conjTranspose *
      Matrix.diagonal (fun i => R.readout () ⟨ι, ⟨ε, ⟨record, a⟩⟩⟩ i))) =
      (1 : Matrix ι ι ℂ)

private theorem actual_law : arena.{u_1, u_2}.Law actual := by
  intro ι ε _ _ _ record hnorm
  change ∑ a, (Matrix.diagonal (fun i => record i a)).conjTranspose *
    Matrix.diagonal (fun i => record i a) = 1
  exact diagonal_kraus_complete record hnorm

private theorem rejected_law : ¬ arena.{u_1, u_2}.Law rejected := by
  intro h
  let ι := ULift.{u_1} (Fin 1)
  let ε := ULift.{u_2} Unit
  have hbad := @h ι ε inferInstance inferInstance inferInstance
    (fun _ _ => (1 : ℂ)) (by intro i; simp)
  have hentry := congrArg
    (fun M => M (ULift.up (0 : Fin 1)) (ULift.up (0 : Fin 1))) hbad
  have : (0 : ℂ) = 1 := by
    simpa [rejected, realize, Matrix.diagonal, Matrix.one_apply, Matrix.mul_apply] using hentry
  exact zero_ne_one this

private theorem dependence : ObservationalDependence signature.{u_1, u_2} actual := by
  intro i
  let p : signature.{u_1, u_2}.Params :=
    ⟨ULift.{u_1} Bool, ⟨ULift.{u_2} Unit,
      ⟨fun b _ => if b.down then 1 else 0, ULift.up ()⟩⟩⟩
  refine ⟨p, ULift.up false, ULift.up true, ?_⟩
  intro he
  simpa [actual, realize, witnessReadout, p] using he

def source_registration : Registration arena.{u_1, u_2}
    (type_of% @diagonal_kraus_complete.{u_1, u_2}) where
  actual := realize arena.signature (fun _ p i => p.2.2.1 i p.2.2.2)
    (fun e _ => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@diagonal_kraus_complete.{u_1, u_2}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro i
      exact nomatch i
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel.diagonal_kraus_complete.{u_1, u_2})
      (Realization signature.{u_1, u_2}) Unit Unit := {
  unitName := `D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel.diagonal_kraus_complete.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_1, u_2}⟩
  objectArena := .source ⟨arena.{u_1, u_2}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_1, u_2} ⟨source_registration.{u_1, u_2}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u_1, u_2}
    (fun _ p i => p.2.2.1 i p.2.2.2) (fun e _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel
    definition := none
    coordinates := #[0, 1, 5, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body",
        "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Decoherence.FiniteShiftedRecordChannel
