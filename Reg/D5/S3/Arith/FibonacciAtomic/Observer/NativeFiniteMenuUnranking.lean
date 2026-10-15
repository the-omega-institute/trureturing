import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuUnranking
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate (height)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuUnranking
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuUnranking

abbrev signature : Signature where
  Params := Menu
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ S i => unrank S i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => .of true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (S : Menu) (i : Nat),
    (N S ≤ i → R.readout () S i = .of true) ∧
    (S = [] → R.readout () S i = .of true ∧ height (R.readout () S i) = 0) ∧
    (i < N S → code S (R.readout () S i) = i) ∧
    (S ≠ [] → height (R.readout () S i) ≤ 1 + S.toFinset.sup List.length)

private theorem root_count : N [[]] = 3 := by
  have g := ((original_code_grammar [[]]).2.1 (by simp)).1
  simpa [child, eta, ((original_code_grammar []).1 rfl).1] using g

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have no := (h [[]] 0).2.2.1 (by rw [root_count]; decide)
  change code [[]] (.of true) = 0 at no
  rw [((original_code_grammar [[]]).2.1 (by simp)).2.2.1] at no
  simpa [child, ((original_code_grammar []).1 rfl).1] using no

def family : Registration arena (type_of% (@original_menu_unranking)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_menu_unranking, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro _
    refine ⟨[[]], 0, 1, ?_⟩
    change unrank [[]] 0 ≠ unrank [[]] 1
    intro he
    have hzero := (original_menu_unranking [[]] 0).2.2.1 (by rw [root_count]; decide)
    have hone := (original_menu_unranking [[]] 1).2.2.1 (by rw [root_count]; decide)
    rw [he, hone] at hzero
    exact Nat.noConfusion hzero

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_menu_unranking) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuUnranking.original_menu_unranking.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuUnranking.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ S i => unrank S i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuUnranking
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuUnranking
