import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer

/-! Typed audit families preserve the whole row functions and original telescopes.
The enrolled readouts select the actual row functions in the source statements.
-/

namespace Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer

open _root_.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace ModFive

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → ZMod 5)

def actual : Realization signature :=
  realize signature (fun _ _ n => row (ZMod 5) n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, r.readout () () n 3 = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  change (0 : ZMod 5) = 1 at hh
  exact (by decide : (0 : ZMod 5) ≠ 1) hh

def family : Registration arena (type_of% @row_mod_five) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨row_mod_five, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have hh := congrFun h 0
    change (1 : ZMod 5) = 0 at hh
    exact (by decide : (1 : ZMod 5) ≠ 0) hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@row_mod_five) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer.ModFive.unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer.ModFive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => row (ZMod 5) n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ModFive

namespace ModFour

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → ZMod 4)

def actual : Realization signature :=
  realize signature (fun _ _ n => row (ZMod 4) n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n k : ℕ, r.readout () () (n + 1) (2 * k + 1) =
    -(∑ s ∈ Finset.range k, r.readout () () n (2 * s + 3)) +
      ((2 * k + 1 : ℕ) : ZMod 4) * r.readout () () n (2 * k + 3)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 1
  change (1 : ZMod 4) = -(∑ s ∈ Finset.range 1, (1 : ZMod 4)) + 3 * 1 at hh
  norm_num at hh
  exact (by decide : (1 : ZMod 4) ≠ 2) hh

def family : Registration arena (type_of% @odd_row_recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨odd_row_recurrence, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have hh := congrFun h 0
    change (1 : ZMod 4) = 0 at hh
    exact (by decide : (1 : ZMod 4) ≠ 0) hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@odd_row_recurrence) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer.ModFour.unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer.ModFour.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => row (ZMod 4) n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ModFour

namespace CatalanFour

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => row ℕ n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, (r.readout () () (n + 1) 3 : ZMod 4) = 3 * (catalan (n + 2) : ZMod 4)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  change (0 : ZMod 4) = 3 * (catalan 2 : ZMod 4) at hh
  norm_num [catalan_succ] at hh
  exact (by decide : (0 : ZMod 4) ≠ 2) hh

def family : Registration arena (type_of% @row_catalan_mod_four) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨row_catalan_mod_four, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have hh := congrFun h 0
    change (1 : ℕ) = 0 at hh
    exact (by decide : (1 : ℕ) ≠ 0) hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@row_catalan_mod_four) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer.CatalanFour.unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer.CatalanFour.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => row ℕ n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CatalanFour

end Reg.D5.S3.Combinatorics.Permutation.BlitvicKammounSteingrimsson14325Transfer
