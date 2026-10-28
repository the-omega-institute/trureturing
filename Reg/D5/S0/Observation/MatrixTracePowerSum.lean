import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Observation.MatrixTracePowerSum
import Reg.Support.DependentFamily

namespace Reg.D5.S0.Observation.MatrixTracePowerSum
open _root_.D5.S0.Observation.MatrixTracePowerSum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Observe the matrix whose shifted power is traced, over its original carrier. -/
abbrev signature : Signature where
  Params := Type u
  State R := Matrix (Fin 2) (Fin 2) R
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ R := Matrix (Fin 2) (Fin 2) R
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ M => M) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ M => fun _ j => M 0 j) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {R : Type u} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (n : Nat),
    Matrix.trace ((r.readout () R M) ^ (n + 2)) =
      Matrix.trace M * Matrix.trace (M ^ (n + 1)) -
        Matrix.det M * Matrix.trace (M ^ n)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} ℤ) inferInstance 1 0
  change Matrix.trace ((!![1, 0; 1, 0] : Matrix (Fin 2) (Fin 2) (ULift.{u} ℤ)) ^ 2) =
    Matrix.trace (1 : Matrix (Fin 2) (Fin 2) (ULift.{u} ℤ)) *
      Matrix.trace (1 : Matrix (Fin 2) (Fin 2) (ULift.{u} ℤ)) -
      Matrix.det (1 : Matrix (Fin 2) (Fin 2) (ULift.{u} ℤ)) *
        Matrix.trace (1 : Matrix (Fin 2) (Fin 2) (ULift.{u} ℤ)) at he
  have hd := congrArg ULift.down he
  norm_num [Matrix.trace_fin_two, Matrix.det_fin_two,
    pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at hd

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} ℤ, 0, 1, ?_⟩
  intro he
  change (0 : Matrix (Fin 2) (Fin 2) (ULift.{u} ℤ)) = 1 at he
  have hd := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ULift.{u} ℤ) => (M 0 0).down) he
  change (0 : ℤ) = 1 at hd
  exact Int.zero_ne_one hd

def source_registration : Registration arena.{u} (type_of% @trace_pow_add_two.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨trace_pow_add_two, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trace_pow_add_two.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S0.Observation.MatrixTracePowerSum.unit
  realizationName := `Reg.D5.S0.Observation.MatrixTracePowerSum.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ M => M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Observation.MatrixTracePowerSum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration


abbrev powArena : Arena where
  signature := signature.{u}
  Law r := ∀ {R : Type u} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ),
    (r.readout () R M) ^ (n + 2) =
      Matrix.trace M • M ^ (n + 1) - Matrix.det M • M ^ n

private theorem powRejected : ¬ powArena.{u}.Law rejected := by
  intro h
  apply rejected_law
  intro R inst M n
  have he := congrArg Matrix.trace (@h R inst M n)
  simpa only [Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul] using he

def powSource : Registration powArena.{u} (type_of% @pow_add_two.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨pow_add_two,rejected,powRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,powRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def powRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@pow_add_two.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S0.Observation.MatrixTracePowerSum.powUnit
  realizationName := `Reg.D5.S0.Observation.MatrixTracePowerSum.powSource
  realizationSource := none
  generated := false
  arena := .source ⟨powArena.{u}⟩
  objectArena := .source ⟨powArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source powArena.{u} ⟨powSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ M => M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Observation.MatrixTracePowerSum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms powSource
#print axioms powRegistration

end
end Reg.D5.S0.Observation.MatrixTracePowerSum
