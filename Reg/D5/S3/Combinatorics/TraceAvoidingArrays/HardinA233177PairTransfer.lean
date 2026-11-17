import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Exact sequence readouts for the literal ladder count and its pair-label transfer. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer (L initial_values)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
attribute [local irreducible] L

namespace Initial
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : Fin 8, R.readout () () (k.val+2) =
      ![162, 1122, 5808, 33702, 186720, 1054446, 5907444, 33206862] k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := initial_values 0
  have hb := h 0
  change (L 2 : ℤ) + 1 = 162 at hb
  norm_num at ha
  linarith
private theorem actual_dependence :
    actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := initial_values 0
  have h3 := initial_values 1
  norm_num at h2 h3
  change (L 2 : ℤ) ≠ (L 3 : ℤ)
  omega
def family : Registration arena (type_of% @initial_values) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@initial_values, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@initial_values) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Initial.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Initial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (L n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Initial

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (L n : ℤ) + if n = 10 then 1 else 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () (n+10) + 6 =
      4 * (R.readout () () (n+9) + 6) + 13 * (R.readout () () (n+8) + 6) -
        19 * (R.readout () () (n+7) + 6) - 22 * (R.readout () () (n+6) + 6) +
        27 * (R.readout () () (n+5) + 6) + 2 * (R.readout () () (n+4) + 6) -
        4 * (R.readout () () (n+3) + 6)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := recurrence 0
  have hb := h 0
  change ((L 10 : ℤ) + 1) + 6 =
    4 * ((L 9 : ℤ) + 0 + 6) + 13 * ((L 8 : ℤ) + 0 + 6) -
      19 * ((L 7 : ℤ) + 0 + 6) - 22 * ((L 6 : ℤ) + 0 + 6) +
      27 * ((L 5 : ℤ) + 0 + 6) + 2 * ((L 4 : ℤ) + 0 + 6) -
      4 * ((L 3 : ℤ) + 0 + 6) at hb
  linarith
private theorem actual_dependence :
    actual.readout () () 2 ≠ actual.readout () () 3 := by
  have h2 := initial_values 0
  have h3 := initial_values 1
  norm_num at h2 h3
  change (L 2 : ℤ) ≠ (L 3 : ℤ)
  omega
def family : Registration arena (type_of% @recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@recurrence, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@recurrence) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Recurrence.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.Recurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (L n : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Recurrence

namespace ColumnRelabel
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 4) (fun _ => Col) (fun _ => Fin 3)
def actual : Realization signature :=
  realize signature (fun _ r c => column c r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (e : Equiv.Perm (Fin 3)) (c : Col) (r : Fin 4),
    column (relabel e c) r = e (R.readout () r c)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (Equiv.refl _) (1,1,1,1) 0
  change (1 : Fin 3) = 0 at hh
  exact (by decide : (1 : Fin 3) ≠ 0) hh
private theorem actual_dependence :
    actual.readout () 0 (0,0,0,0) ≠ actual.readout () 0 (1,1,1,1) := by
  decide

def family : Registration arena (type_of% @column_relabel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@column_relabel, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨0, (0,0,0,0), (1,1,1,1), actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@column_relabel) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.ColumnRelabel.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.ColumnRelabel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ColumnRelabel

namespace ClassRelabel
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Col) (fun _ => Fin 14)
def actual : Realization signature :=
  realize signature (fun _ _ c => cls c) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 13) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (e : Equiv.Perm (Fin 3)) (c : Col),
    cls (relabel e c) = R.readout () () c
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (Equiv.refl _) (0,0,0,0)
  change (0 : Fin 14) = 13 at hh
  exact (by decide : (0 : Fin 14) ≠ 13) hh
private theorem actual_dependence :
    actual.readout () () (0,0,0,0) ≠ actual.readout () () (0,0,0,1) := by
  decide

def family : Registration arena (type_of% @class_relabel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@class_relabel, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), (0,0,0,0), (0,0,0,1), actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@class_relabel) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.ClassRelabel.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.ClassRelabel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ClassRelabel

namespace ClassRep
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Col) (fun _ => Col)
def actual : Realization signature :=
  realize signature (fun _ _ c => representatives (cls c)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0,0,0,1)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ c : Col, ∃ e : Equiv.Perm (Fin 3), relabel e c = R.readout () () c
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, he⟩ := h (0,0,0,0)
  have h0 := congrArg Prod.fst he
  have h1 := congrArg (fun c : Col => c.2.2.2) he
  change e 0 = 0 at h0
  change e 0 = 1 at h1
  exact (by decide : (0 : Fin 3) ≠ 1) (h0.symm.trans h1)
private theorem actual_dependence :
    actual.readout () () (0,0,0,0) ≠ actual.readout () () (0,0,0,1) := by
  decide

def family : Registration arena (type_of% @class_rep) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@class_rep, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), (0,0,0,0), (0,0,0,1), actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@class_rep) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.ClassRep.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.ClassRep.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ClassRep

namespace ColumnGrid
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ n : ℕ, Fin 4 × Fin n → Fin 3) (fun p => Fin 4 × Fin p.1) (fun _ => Fin 3)
def actual : Realization signature :=
  realize signature (fun _ p c => p.2 c) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (P : Fin 4 × Fin n → Fin 3) (j : Fin n) (r : Fin 4),
    column (gridEquiv n P j) r = R.readout () ⟨n, P⟩ (r,j)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (fun _ => 0) 0 0
  change (0 : Fin 3) = 2 at hh
  exact (by decide : (0 : Fin 3) ≠ 2) hh
private theorem actual_dependence :
    actual.readout () ⟨1, fun p => if p.1 = 0 then 0 else 1⟩ (0,0) ≠
      actual.readout () ⟨1, fun p => if p.1 = 0 then 0 else 1⟩ (1,0) := by
  decide

def family : Registration arena (type_of% @column_grid) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@column_grid, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    exact ⟨⟨1, fun p => if p.1 = 0 then 0 else 1⟩, (0,0), (1,0), actual_dependence⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@column_grid) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.ColumnGrid.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.ColumnGrid.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ColumnGrid
end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
