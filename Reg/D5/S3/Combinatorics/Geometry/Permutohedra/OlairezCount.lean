import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.Permutohedra.OlairezCount
import Reg.Support.DependentFamily

/-! The terminal sum, read from the dilation at fixed coordinate count. -/

namespace Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezCount

open _root_.OlairezCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ n k => terminalSum n k) (fun e => nomatch e)

private def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ), 3 ≤ n →
    Finite (SourcePoints n k) ∧ Nat.card (SourcePoints n k) = R.readout () n k

private theorem terminal_four_zero : terminalSum 4 0 = 1 := by decide

private theorem zeroReadout_fails : ¬ arena.Law zeroReadout := by
  intro law
  have h := (law 4 0 (by decide)).2
  change Nat.card (SourcePoints 4 0) = 0 at h
  rw [(latticePointCount_terminalSum 4 0 (by decide)).2, terminal_four_zero] at h
  omega

private theorem terminal_four_dilations_differ : terminalSum 4 0 ≠ terminalSum 4 1 :=
  fun h => (by decide : (1 : ℕ) ≠ 22)
    (terminal_four_zero.symm.trans (h.trans recurrence_four_one))

def family : Registration arena (type_of% (@_root_.OlairezCount.latticePointCount_terminalSum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨latticePointCount_terminalSum, zeroReadout, zeroReadout_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroReadout, ?_, rfl, zeroReadout_fails⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨4, 0, 1, by
      simpa only [actual, realize] using terminal_four_dilations_differ⟩

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.OlairezCount.latticePointCount_terminalSum) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `OlairezCount.latticePointCount_terminalSum
      "Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezCount/Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezCount.arena/[anonymous]")
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => terminalSum n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.Permutohedra.OlairezCount
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{name := `Elab.async, value := .bool true},
    {name := `internal.cmdlineSnapshots, value := .bool true},
    {name := `linter.mathlibStandardSet, value := .bool true},
    {name := `maxSynthPendingDepth, value := .nat 3},
    {name := `pp.unicode.fun, value := .bool true},
    {name := `relaxedAutoImplicit, value := .bool false}] }

/-! The closed utility equation observes the terminal recurrence at dilation one. -/
namespace FourOne

private abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ k => terminalSum 4 k) (fun e => nomatch e)

private def zeroReadout : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 1 = 22

private theorem zeroReadout_fails : ¬ arena.Law zeroReadout := by
  intro h
  change (0 : ℕ) = 22 at h
  omega

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
def family : Registration arena (type_of% (@_root_.OlairezCount.recurrence_four_one)) where
  actual := actual
  bridge := by
    change terminalSum 4 1 = 22 ↔ terminalSum 4 1 = 22
    exact Iff.rfl
  variation := ⟨recurrence_four_one, zeroReadout, zeroReadout_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨zeroReadout, ?_, rfl, zeroReadout_fails⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, terminal_four_dilations_differ⟩

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.OlairezCount.recurrence_four_one) (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    (Lean.Name.str `OlairezCount.recurrence_four_one
      "Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezCount/Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezCount.FourOne.arena/[anonymous]")
    "__information_unit"
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezCount.FourOne.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => terminalSum 4 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.Permutohedra.OlairezCount
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{name := `Elab.async, value := .bool true},
    {name := `internal.cmdlineSnapshots, value := .bool true},
    {name := `linter.mathlibStandardSet, value := .bool true},
    {name := `maxSynthPendingDepth, value := .nat 3},
    {name := `pp.unicode.fun, value := .bool true},
    {name := `relaxedAutoImplicit, value := .bool false}] }

end FourOne

end Reg.D5.S3.Combinatorics.Geometry.Permutohedra.OlairezCount
