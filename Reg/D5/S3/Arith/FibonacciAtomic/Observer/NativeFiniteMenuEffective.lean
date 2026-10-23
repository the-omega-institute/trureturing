import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuEffective
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate (height)
open D5.S3.Arith.FibonacciAtomic.Observer
open NativeFiniteMenuCode NativeFiniteMenuReconstruction NativeFiniteMenuEffective
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuEffective

abbrev signature : Signature where
  Params := Menu
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ S u => code S u) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : Nat) (S : Menu) (closed : PrefixClosed S)
    (depth : ∀ q ∈ S, q.length < D),
    Computable₂ (decode D S) ∧
    (∀ u : Source, ∀ k : Nat, decode D S (initial S u) k = future S u k) ∧
    Primrec₂ (rawDecode D S) ∧ Computable₂ (rawDecode D S) ∧
    (∀ xs k, rawValid S xs = false → rawDecode D S xs k = List.replicate S.length .absent) ∧
    (∀ xs k, restore D S (xs.map rawReply) = none →
      rawDecode D S xs k = List.replicate S.length .absent) ∧
    (∀ u : Source, ∀ k : Nat, rawDecode D S (rawVector S u) k = future S u k) ∧
    (∀ u v : Source, initial S u = initial S v → R.readout () S u = code S v) ∧
    (∀ xs t, restore D S xs = some t → height t ≤ D ∧ initial S t = xs) ∧
    (∀ xs, restore D S xs = none ↔ ¬ ∃ u : Source, initial S u = xs)

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
  have z := h 1 [[]] closed (by intro q hq; simp at hq; subst q; decide)
  have no := z.2.2.2.2.2.2.2.1 (.of true) (.of true) rfl
  have hc := ((original_code_grammar [[]]).2.1 (by simp)).2.2.1
  change (0 : Nat) = code [[]] (.of true) at no
  rw [hc] at no
  have nl := (original_code_grammar (child false [[]])).2.2.1
  have nr := (original_code_grammar (child true [[]])).2.2.1
  nlinarith

def family : Registration arena (type_of% (@total_native_menu_decoder)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨total_native_menu_decoder, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨[[]], .of true, .of false, ?_⟩
    exact original_code_context_separation [[]] [] [] (by simp)

noncomputable def total_native_menu_decoder_registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@total_native_menu_decoder) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuEffective.total_native_menu_decoder.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuEffective.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuEffective
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","body","body","arg","arg","arg","arg","arg","arg","arg","fn","arg","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms total_native_menu_decoder_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuEffective
