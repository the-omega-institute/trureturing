import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound four-slot registrations with literal unknown residuals. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

namespace GridGood
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Fin 4 × Fin n → Fin 3) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ n P => @decide (@Proper n P) (Classical.propDecidable _))
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (P : Fin 4 × Fin n → Fin 3), R.readout () n P = true ↔
      _root_.D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix.good compatible
        (fun _ _ _ => True) (List.ofFn (gridEquiv n P))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : Proper (n := 0) (fun _ => 0) := by
    intro j
    exact Fin.elim0 j
  exact Bool.noConfusion ((h 0 (fun _ => 0)).mpr ((grid_good 0 (fun _ => 0)).mp hp))
def family : Registration arena (type_of% @grid_good) where
  actual := actual
  bridge := by
    classical
    simp only [actual, realize, decide_eq_true_eq]
  variation := ⟨by
    classical
    simpa only [actual, realize, decide_eq_true_eq] using @grid_good,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    classical
    intro i
    refine ⟨2, (fun x => if x.2 = 0 then 0 else 1), (fun _ => 0), ?_⟩
    have hg : Proper (fun x : Fin 4 × Fin 2 => if x.2 = 0 then 0 else 1) := by
      unfold Proper
      decide +kernel
    have hb : ¬ Proper (fun _ : Fin 4 × Fin 2 => 0) := by
      unfold Proper
      decide +kernel
    simp only [actual, realize, hg, hb, decide_true, decide_false]
    decide
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@grid_good) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore.GridGood.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore.GridGood.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n P => @decide (@Proper n P) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end GridGood

namespace CompatibleRelabel
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Col
    (fun _ => Col) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ a b => decide (compatible a b)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (e : Equiv.Perm (Fin 3)) (a b : Col),
      compatible (relabel e a) (relabel e b) ↔ R.readout () a b = true
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : compatible (0, 0, 0, 0) (1, 1, 1, 1) := by
    unfold compatible column
    decide +kernel
  exact Bool.noConfusion ((h (Equiv.refl _) (0, 0, 0, 0) (1, 1, 1, 1)).mp
    ((compatible_relabel (Equiv.refl _) _ _).mpr hp))
def family : Registration arena (type_of% @compatible_relabel) where
  actual := actual
  bridge := by
    simp only [actual, realize, decide_eq_true_eq]
  variation := ⟨by
    simpa only [actual, realize, decide_eq_true_eq] using @compatible_relabel,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(0, 0, 0, 0), (1, 1, 1, 1), (0, 0, 0, 0), ?_⟩
    have hg : compatible (0, 0, 0, 0) (1, 1, 1, 1) := by
      unfold compatible column
      decide +kernel
    have hb : ¬ compatible (0, 0, 0, 0) (0, 0, 0, 0) := by
      unfold compatible column
      decide +kernel
    simp only [actual, realize, hg, hb, decide_true, decide_false]
    decide
def audit : Contract.Registration.{0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@compatible_relabel) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore.CompatibleRelabel.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore.CompatibleRelabel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a b => decide (compatible a b)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CompatibleRelabel

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
