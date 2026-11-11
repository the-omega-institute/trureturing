import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound four-slot registrations with literal unknown residuals. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer (Col column gridEquiv relabel)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

namespace GridGood
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Fin 4 × Fin n → Fin 3) (fun n => Fin n → Col)
def actual : Realization signature :=
  realize signature (fun _ n P => gridEquiv n P) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ n _ => gridEquiv n (fun _ => 0)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (P : Fin 4 × Fin n → Fin 3), Proper P ↔
      _root_.D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix.good compatible
        (fun _ _ _ => True) (List.ofFn (R.readout () n P))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hg : Proper (fun x : Fin 4 × Fin 2 => if x.2 = 0 then 0 else 1) := by
    unfold Proper
    decide +kernel
  have hb : ¬ Proper (fun _ : Fin 4 × Fin 2 => 0) := by
    unfold Proper
    decide +kernel
  exact hb ((grid_good 2 (fun _ => 0)).mpr ((h 2 _).mp hg))
def family : Registration arena (type_of% @grid_good) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@grid_good, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
    intro he
    have hh := congrFun ((gridEquiv 1).injective he) ((0 : Fin 4), (0 : Fin 1))
    norm_num at hh
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
  readout := some (realize signature (fun _ n P => gridEquiv n P) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end GridGood

namespace CompatibleRelabel
abbrev signature : Signature.{0, 0, 0, 0, 0} :=
  _root_.Reg.Support.SingleDependentReadout.signature (Equiv.Perm (Fin 3))
    (fun _ => Col) (fun _ => Col)
def actual : Realization signature :=
  realize signature (fun _ e b => relabel e b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 0, 0, 0)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (e : Equiv.Perm (Fin 3)) (a b : Col),
      compatible (R.readout () e a) (R.readout () e b) ↔ compatible a b
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hg : compatible (0, 0, 0, 0) (1, 1, 1, 1) := by
    unfold compatible column
    decide +kernel
  have hb : ¬ compatible (0, 0, 0, 0) (0, 0, 0, 0) := by
    unfold compatible column
    decide +kernel
  exact hb ((h (Equiv.refl _) (0, 0, 0, 0) (1, 1, 1, 1)).mpr hg)
def family : Registration arena (type_of% @compatible_relabel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@compatible_relabel, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨Equiv.refl _, (0, 0, 0, 0), (1, 1, 1, 1), ?_⟩
    intro he
    have hh := congrArg Prod.fst ((relabel (Equiv.refl _)).injective he)
    norm_num at hh
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
  readout := some (realize signature (fun _ e b => relabel e b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CompatibleRelabel

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
