import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Summation
import Reg.Support.SingleDependentReadout

/-! The order observation in the exact connected-support moments. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Summation

open _root_.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ConnectedSets G500) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ S => Nat.card S.val) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (Nat.card (ConnectedSets G500),
      (letI : Fintype (ConnectedSets G500) := Fintype.ofFinite _
       ∑ S : ConnectedSets G500, R.readout () () S)) = (10425438990512, 43855001336852520)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg Prod.snd h
  change (letI : Fintype (ConnectedSets G500) := Fintype.ofFinite _
       ∑ _S : ConnectedSets G500, (0 : ℕ)) = 43855001336852520 at he
  simp only [Finset.sum_const_zero] at he
  exact (by decide : (0 : ℕ) ≠ 43855001336852520) he

private def singletonConfig : Configuration := .firstOnly ⟨(0, 0), le_rfl⟩
private def twoVertexConfig : Configuration := .firstOnly ⟨(0, 1), by decide⟩

def family : Registration arena (type_of% @induced_exact_moments) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨induced_exact_moments, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), supportEquiv.symm singletonConfig, supportEquiv.symm twoVertexConfig, ?_⟩
    change Nat.card (supportEquiv.symm singletonConfig).val ≠ Nat.card (supportEquiv.symm twoVertexConfig).val
    rw [supportEquiv_order, supportEquiv_order]
    change (1 : ℕ) ≠ 2
    decide

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
    (@induced_exact_moments) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement.induced_exact_moments.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Summation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => Nat.card S.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Summation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Summation
