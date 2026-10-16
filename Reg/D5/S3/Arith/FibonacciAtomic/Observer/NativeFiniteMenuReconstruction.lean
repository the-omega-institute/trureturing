import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuReconstruction
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate (height)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuReconstruction
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuReconstruction

abbrev signature : Signature where
  Params := Menu
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ S u => code S u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (h : Nat) (S : Menu) (u : Source) (f : Address → Reply),
    PrefixClosed S → (∀ q ∈ S, q.length < h) → (∀ q ∈ S, f q = readout q u) →
    ∃ t : Source, reconstruct h S f = some t ∧ height t ≤ h ∧ R.readout () S t = code S u ∧
      ∀ q ∈ S, ∀ k : Nat, readout q (substitution^[k] t) = readout q (substitution^[k] u)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have closed : PrefixClosed ([[]] : Menu) := by
    intro q hq a ha
    have hqn : q = [] := by simpa using hq
    subst q
    obtain ⟨r,he⟩ := ha
    have hh := congrArg List.length he
    simp only [List.length_append, List.length_nil] at hh
    have han : a = [] := List.length_eq_zero_iff.mp (by omega)
    subst a
    simp
  obtain ⟨t, _, _, no, _⟩ := h 1 [[]] (.of true)
    (fun q => readout q (.of true)) closed
    (by intro q hq; simp only [List.mem_singleton] at hq; subst q; decide)
    (by intro q _; rfl)
  change (0 : Nat) = code [[]] (.of true) at no
  have hc := ((original_code_grammar [[]]).2.1 (by simp)).2.2.1
  rw [hc] at no
  have nl := (original_code_grammar (child false [[]])).2.2.1
  have nr := (original_code_grammar (child true [[]])).2.2.1
  nlinarith

def family : Registration arena (type_of% (@prefix_menu_reconstruction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prefix_menu_reconstruction, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨[[]], .of true, .of false, ?_⟩
    exact original_code_context_separation [[]] [] [] (by simp)

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prefix_menu_reconstruction) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuReconstruction.prefix_menu_reconstruction.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuReconstruction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ S u => code S u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuReconstruction
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","arg","body","arg","arg","fn","arg","fn","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuReconstruction
