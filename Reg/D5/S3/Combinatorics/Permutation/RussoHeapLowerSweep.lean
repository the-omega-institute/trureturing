import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep

/-! # Auditing the penultimate net on its full finite carrier -/

namespace Reg.D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep

open Equiv Equiv.Perm LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep

/-- The actual penultimate net, read at each point of its full carrier. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun m => Fin (2*m+2)) (fun _ => ℕ)

def observe (_ : signature.Role) (m : ℕ) (x : Fin (2*m+2)) : ℕ :=
  (actualU (2*m+2) x).val

def actual : Realization signature := realize signature observe (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 2 ≤ m → ∀ x : Fin (2*m+2), R.readout () m x = uArrow m x.val

def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 2 (by decide) (4 : Fin 6)
  change 0 = 1 at he
  contradiction

set_option maxRecDepth 4096 in
private theorem observation_varies : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, (4 : Fin 6), (5 : Fin 6), ?_⟩
  change (actualU 6 (4 : Fin 6)).val ≠ (actualU 6 (5 : Fin 6)).val
  intro he
  have h4 := literal_net_value 2 (by decide) (4 : Fin 6)
  have h5 := literal_net_value 2 (by decide) (5 : Fin 6)
  have h14 : (actualU 6 (4 : Fin 6)).val = 1 := h4
  have h55 : (actualU 6 (5 : Fin 6)).val = 5 := h5
  exact (by decide : (1 : ℕ) ≠ 5) (h14.symm.trans (he.trans h55))

def family : Registration arena (type_of% (@literal_net_value)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@literal_net_value, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := observation_varies

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@literal_net_value) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep.literal_net_value.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observe (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Slot

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun n => Fin n) (fun _ => ℕ)

def observe (_ : signature.Role) (n : ℕ) (x : Fin n) : ℕ := x.val

def actual : Realization signature := realize signature observe (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n i : ℕ} [NeZero n], i < n → R.readout () n (slot n i) = i

def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (by decide : (0 : ℕ) ≠ 1) (@h 2 1 inferInstance (by decide))

private theorem observation_varies : ObservationalDependence signature actual := by
  intro role
  cases role
  exact ⟨2, 0, 1, by decide⟩

def family : Registration arena (type_of% (@slot_val)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@slot_val, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := observation_varies

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@slot_val) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep.slot_val.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep.Slot.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observe (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Slot

namespace PrefixNet

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => List (Fin n × Fin n)) (fun n => Perm (Fin n))

def observe (_ : signature.Role) (n : ℕ) (swaps : List (Fin n × Fin n)) :
    Perm (Fin n) :=
  executeSwaps swaps 1

def actual : Realization signature := realize signature observe (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N k : ℕ} {lower : List (Fin N × Fin N)}, PrefixSweep k lower →
    FixesOutside k (R.readout () N lower)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Fin.revPerm) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hl : PrefixSweep 1 ([] : List (Fin 2 × Fin 2)) := cyclic_prefixSweep 2 0 (by decide)
  have he := h hl (1 : Fin 2) (by decide)
  exact (by decide : Fin.revPerm (1 : Fin 2) ≠ 1) he

private theorem observation_varies : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, [], [(0, 1)], ?_⟩
  intro he
  have hs := congrArg (fun p : Perm (Fin 2) => p 0) he
  exact (by decide : (0 : Fin 2) ≠ 1) hs

def family : Registration arena (type_of% (@prefixNet_fixes)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prefixNet_fixes, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := observation_varies

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@prefixNet_fixes) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep.prefixNet_fixes.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep.PrefixNet.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observe (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrefixNet

end Reg.D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep
