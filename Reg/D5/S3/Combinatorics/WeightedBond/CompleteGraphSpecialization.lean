import LeanInformationAuditInterface.Contract.Registration
import Reg.D5.S3.Combinatorics.WeightedBond.CountableColors
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of both complete-graph coefficient conventions. -/

open _root_.D5.S3.Combinatorics.WeightedBond PowerSeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.WeightedBond.CompleteGraphSpecialization

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => Mark)

def actual : Realization signature :=
  realize signature (fun _ q n => sourceSpecialization n (q + 2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n q : ℕ,
    R.readout () q (n + 1) =
      (n.factorial : Mark) * coeff n
        (rescale (1 - (n + 1 : Mark) * Polynomial.X) (PowerSeries.exp Mark) *
          reciprocalFactor q Polynomial.X ^ (n + 1)) ∧
    reversePsi (n + 1) (q + 2) =
      (n.factorial : Mark) * coeff n
        (rescale (Polynomial.X - (n + 1 : Mark)) (PowerSeries.exp Mark) *
          reciprocalFactor q 1 ^ (n + 1)) ∧
    reversePsi (n + 1) (q + 2) = (sourceSpecialization (n + 1) (q + 2)).reflect n ∧
    (reversePsi (n + 1) (q + 2)).eval 0 =
      (sourceSpecialization (n + 1) (q + 2)).coeff n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 0 0).1
  have good := (result 0 0).1
  change (0 : Mark) = _ at bad
  exact zero_ne_one (bad.trans (good.symm.trans CountableColors.source_one_two))

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨0, 1, 2, CountableColors.source_dependence⟩

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    result (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.WeightedBond.CompleteGraphSpecialization.specialization
  realizationName := `Reg.D5.S3.Combinatorics.WeightedBond.CompleteGraphSpecialization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q n => sourceSpecialization n (q + 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.WeightedBond.CompleteGraphSpecialization
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.WeightedBond.CompleteGraphSpecialization
end
