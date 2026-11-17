import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The complete original positive-height recurrence as a dependent-family law. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence (result)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer (a)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255ShapeSymmetry
  (K F literal_canonical_bridge)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ+) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ h => (a h : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ h => (a h : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 6 ≤ n),
    R.readout () () ⟨n, by omega⟩ =
      5504 * R.readout () () ⟨n - 1, by omega⟩ -
      6438912 * R.readout () () ⟨n - 2, by omega⟩ +
      2774532096 * R.readout () () ⟨n - 3, by omega⟩ -
      478351982592 * R.readout () () ⟨n - 4, by omega⟩ +
      27831388078080 * R.readout () () ⟨n - 5, by omega⟩
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := result 6 (by decide)
  have hb := h 6 (by decide)
  change (a ⟨6, by decide⟩ : ℤ) + 1 =
    5504 * ((a ⟨5, by decide⟩ : ℤ) + 1) -
    6438912 * ((a ⟨4, by decide⟩ : ℤ) + 1) +
    2774532096 * ((a ⟨3, by decide⟩ : ℤ) + 1) -
    478351982592 * ((a ⟨2, by decide⟩ : ℤ) + 1) +
    27831388078080 * ((a ⟨1, by decide⟩ : ℤ) + 1) at hb
  linarith
set_option maxRecDepth 20000 in
private theorem actual_dependence :
    actual.readout () () ⟨1, by decide⟩ ≠ actual.readout () () ⟨2, by decide⟩ := by
  change (a ⟨1, by decide⟩ : ℤ) ≠ (a ⟨2, by decide⟩ : ℤ)
  have ha0 := literal_canonical_bridge 0
  have hb := literal_canonical_bridge 1
  have ha : (a ⟨1, by decide⟩ : ℤ) = 528 := by
    calc
      _ = (16 : ℤ) * 128^0 + 32 * ∑ i : Fin 16, F 0 i := ha0
      _ = 528 := by norm_num [F, Matrix.one_mulVec]
  have hF (i : Fin 16) : 0 ≤ F 1 i := by
    simp only [F, pow_one]
    apply mul_nonneg (by norm_num)
    unfold Matrix.mulVec dotProduct
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg ?_ (by norm_num)
    unfold K
    apply Finset.sum_nonneg
    intro q _
    split_ifs <;> norm_num
  have hs : 0 ≤ ∑ i : Fin 16, F 1 i := Finset.sum_nonneg (fun i _ => hF i)
  simp only [pow_one] at hb
  intro he
  rw [← he] at hb
  linarith
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), ⟨1, by decide⟩, ⟨2, by decide⟩, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ h => (a h : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255Recurrence
