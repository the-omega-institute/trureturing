import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.Permutation.RussoExtremalHeap

/-! # Auditing the exact ordered list of extremal Heap arrays -/

namespace Reg.D5.S3.Combinatorics.Permutation.RussoExtremalHeap

open Equiv Equiv.Perm LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Permutation.RussoHeapLowerSweep
open _root_.D5.S3.Combinatorics.Permutation.RussoExtremalHeap

/-- The emitted array list at each ordered physical swap list. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => List (Fin n × Fin n)) (fun n => List (Perm (Fin n)))

def observe (_ : signature.Role) (n : ℕ) (swaps : List (Fin n × Fin n)) :
    List (Perm (Fin n)) :=
  sweepArrays swaps 1

def actual : Realization signature := realize signature observe (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (extremalSweep 2 = [(0, 1)] ∧ sweepArrays (extremalSweep 2) 1 = [1, Fin.revPerm]) ∧
    ∀ (n : ℕ) (hn : 2 ≤ n), n % 4 = 2 →
      letI : NeZero n := ⟨by omega⟩
      let swaps := extremalSweep n
      let emitted := R.readout () n swaps
      emitted.head? = some 1 ∧
        emitted.Nodup ∧
        (∀ array : Perm (Fin n), array ∈ emitted) ∧
        emitted.length = n.factorial ∧
        emitted.IsChain (fun p q => ∃ a b, a ≠ b ∧ q = p * swap a b) ∧
        (∀ i : ℕ, emitted[i+1]? = (emitted[i]?).bind fun array =>
          swaps[i]?.map fun ab => array * swap ab.1 ab.2) ∧
        emitted.getLast? = some Fin.revPerm ∧
        (executeSwaps swaps 1)⁻¹ = Fin.revPerm ∧
        (∀ array : Perm (Fin n), array = Fin.revPerm ∨
          Pi.Lex (· < ·) (· < ·) (fun i => array i) (fun i => Fin.rev i)) ∧
      (∀ ab ∈ swaps, ab.1 ≠ ab.2) ∧
      (6 ≤ n →
        (literalZ n).IsCycleOn Set.univ ∧
        Function.Bijective (fun j : Fin n => (literalZ n ^ j.val) (slot n (n-1))) ∧
        (∀ j < n-1, (extremalTopPartner n j).val < n-1) ∧
        executeSwaps swaps 1 = actualU n ^ n * literalZ n ∧
        actualU n ^ n * literalZ n = Fin.revPerm ∧
        (∀ j < n-1,
          let lower := penultimateSweep n
          let previous := orderedSweep lower (slot n (n-1)) (extremalTopPartner n) j
          let last := executeSwaps previous 1
          let τ := swap (extremalTopPartner n j) (slot n (n-1))
          sweepArrays (orderedSweep lower (slot n (n-1)) (extremalTopPartner n) (j+1)) 1 =
              sweepArrays previous 1 ++ sweepArrays lower (τ * last) ∧
            (sweepArrays previous 1).getLast? = some last⁻¹ ∧
            (sweepArrays lower (τ * last)).head? = some (last⁻¹ * τ)))

def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h.2 2 (by decide) (by decide)).1
  change none = some (1 : Perm (Fin 2)) at he
  contradiction

private theorem observation_varies : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, [], [(0, 1)], ?_⟩
  intro he
  have heq := congrArg List.length he
  change 1 = 2 at heq
  contradiction

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := observation_varies

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@result) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.RussoExtremalHeap.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.RussoExtremalHeap.family
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
    owner := `D5.S3.Combinatorics.Permutation.RussoExtremalHeap
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Permutation.RussoExtremalHeap
