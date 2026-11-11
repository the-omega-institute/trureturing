import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.A308815DFiniteRecurrence
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Recurrence.A308815DFiniteRecurrence
open _root_.D5.S1.Recurrence.A308815DFiniteRecurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => PowerSeries ℚ) (fun _ => PowerSeries ℚ)

abbrev c : PowerSeries ℚ := PowerSeries.catalanSeries.map (Nat.castRingHom ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ f => derivative (R := ℚ) f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := X * (1 - 4 * X) * R.readout () () c + (1 - 2 * X) * c = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (coeff 1) h
  norm_num [rejected, realize, c, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ] at he

def family : Registration arena (type_of% cat_ode) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cat_ode, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, X, ?_⟩
    change derivative (R := ℚ) 0 ≠ derivative X
    simp

def catOdeAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    cat_ode (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.A308815DFiniteRecurrence.catOdeUnit
  realizationName := `Reg.D5.S1.Recurrence.A308815DFiniteRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => derivative (R := ℚ) f)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (PowerSeries ℚ)
  sourceSelection := some {
    owner := `D5.S1.Recurrence.A308815DFiniteRecurrence
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms catOdeAudit
end
end Reg.D5.S1.Recurrence.A308815DFiniteRecurrence
