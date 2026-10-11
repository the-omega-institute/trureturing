import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
noncomputable section

abbrev choiceSignature : Signature.{0,0,0,0,0} where
  Params := Bool → List Label
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def choiceActual : Realization choiceSignature :=
  realize choiceSignature (fun _ R zs => (choiceBlocks R zs).length) (fun e => nomatch e)
def choiceRejected : Realization choiceSignature :=
  realize choiceSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev choiceArena : Arena.{0,0,0,0,0} where
  signature := choiceSignature
  Law r :=
    ∀ (R : Bool → List Label) (W : Bool → List Color)
      (hlen : ∀ i, (R i).length = (W i).length) (zs : List Bool),
      r.readout () R zs = (choiceBlocks W zs).length

theorem choice_rejected_law : ¬ choiceArena.Law choiceRejected := by
  intro h
  have hh := h (fun _ => []) (fun _ => []) (fun _ => rfl) []
  norm_num [choiceRejected, realize, choiceBlocks] at hh

def choiceRegistration : Registration choiceArena (type_of% @choice_lengths) where
  actual := choiceActual
  bridge := Iff.rfl
  variation := ⟨@choice_lengths, choiceRejected, choice_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨choiceRejected, ?_, rfl, choice_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(fun _ => [Label.L0]), [], [false], ?_⟩
    simp [choiceActual, realize, choiceBlocks]

def choice_lengths_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.choice_lengths)
      (type_of% (realize.{0,0,0,0,0} choiceSignature
        (fun _ R zs => (choiceBlocks R zs).length) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.choice_lengths_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.choiceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨choiceArena⟩
  objectArena := .source ⟨choiceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source choiceArena ⟨choiceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} choiceSignature
    (fun _ R zs => (choiceBlocks R zs).length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms choiceRegistration
#print axioms choice_lengths_registration

abbrev prefixSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : List Label, ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def prefixActual : Realization prefixSignature :=
  realize prefixSignature (fun _ q p => compose (q.1.drop p) q.2) (fun e => nomatch e)
def prefixRejected : Realization prefixSignature :=
  realize prefixSignature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

abbrev prefixArena : Arena.{0,0,0,0,0} where
  signature := prefixSignature
  Law r :=
    ∀ (A : List Label) (beta : ℕ → Label) (X : ℕ → ℝ)
      (z : ℝ) (prefixLabels : ∀ p (hp : p < A.length), beta p = A[p])
      (recurrence : ∀ p, X p = branch (beta p) (X (p+1)))
      (terminal : X A.length = z),
      ∀ p, p ≤ A.length → X p = r.readout () ⟨A,z⟩ p

theorem prefix_rejected_law : ¬ prefixArena.Law prefixRejected := by
  intro h
  have hh := h [] (fun _ => Label.L0) (fun _ => 0) 0
    (by intro p hp; simp at hp)
    (by intro p; simp [branch, shift]) rfl 0 (by simp)
  norm_num [prefixRejected, realize] at hh

def prefixRegistration : Registration prefixArena (type_of% @prefix_coordinates) where
  actual := prefixActual
  bridge := Iff.rfl
  variation := ⟨@prefix_coordinates, prefixRejected, prefix_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨prefixRejected, ?_, rfl, prefix_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨[Label.L2], 0⟩, 0, 1, ?_⟩
    norm_num [prefixActual, realize, compose, branch, shift]

def prefix_coordinates_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.prefix_coordinates)
      (type_of% (realize.{0,0,0,0,0} prefixSignature
        (fun _ q p => compose (q.1.drop p) q.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.prefix_coordinates_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.prefixRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨prefixArena⟩
  objectArena := .source ⟨prefixArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source prefixArena ⟨prefixRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} prefixSignature
    (fun _ q p => compose (q.1.drop p) q.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms prefixRegistration
#print axioms prefix_coordinates_registration

abbrev synchronousSignature : Signature.{1,0,0,0,0} where
  Params := Σ A : Type, Σ _ : (Bool → List A), Σ n : ℕ, (Fin n → Bool)
  State q := List q.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def synchronousActual : Realization synchronousSignature :=
  realize synchronousSignature (fun _ q P => (synchronousPrefix P q.2.1 q.2.2.2).length) (fun e => nomatch e)
def synchronousRejected : Realization synchronousSignature :=
  realize synchronousSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev synchronousArena : Arena.{1,0,0,0,0} where
  signature := synchronousSignature
  Law r :=
    ∀ {A : Type} (P : List A) (R : Bool → List A)
      (L : ℕ) (hlen : ∀ i, (R i).length = L) (n : ℕ) (z : Fin n → Bool),
      r.readout () ⟨A,⟨R,⟨n,z⟩⟩⟩ P = P.length + n*L

theorem synchronous_rejected_law : ¬ synchronousArena.Law synchronousRejected := by
  intro h
  have hh := @h Unit [] (fun _ => []) 0 (fun _ => rfl) 0 (fun j => Fin.elim0 j)
  norm_num [synchronousRejected, realize] at hh

def synchronousRegistration : Registration synchronousArena (type_of% @synchronous_length) where
  actual := synchronousActual
  bridge := Iff.rfl
  variation := ⟨@synchronous_length, synchronousRejected, synchronous_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨synchronousRejected, ?_, rfl, synchronous_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨Unit, ⟨(fun _ => []), ⟨0, (fun j => Fin.elim0 j)⟩⟩⟩, [], [()], ?_⟩
    simp [synchronousActual, realize, synchronousPrefix]

def synchronous_length_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,1,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.synchronous_length)
      (type_of% (realize.{1,0,0,0,0} synchronousSignature
        (fun _ q P => (synchronousPrefix P q.2.1 q.2.2.2).length) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.synchronous_length_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.synchronousRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨synchronousArena⟩
  objectArena := .source ⟨synchronousArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source synchronousArena ⟨synchronousRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{1,0,0,0,0} synchronousSignature
    (fun _ q P => (synchronousPrefix P q.2.1 q.2.2.2).length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
    definition := none
    coordinates := #[0, 2, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms synchronousRegistration
#print axioms synchronous_length_registration

abbrev addressSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : List Label, List Label
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Label
  Anchor := Empty
  finiteAnchor := inferInstance

def addressActual : Realization addressSignature :=
  realize addressSignature (fun _ q p => address (q.1 ++ q.2) p) (fun e => nomatch e)
def addressRejected : Realization addressSignature :=
  realize addressSignature (fun _ _ _ => Label.L3) (fun e => nomatch e)

abbrev addressArena : Arena.{0,0,0,0,0} where
  signature := addressSignature
  Law r :=
    ∀ (A w : List Label) (p : ℕ) (hp : p < A.length),
      r.readout () ⟨A,w⟩ p = A[p]

theorem address_rejected_law : ¬ addressArena.Law addressRejected := by
  intro h
  have hh := h [Label.L0] [] 0 (by simp)
  simp [addressRejected, realize] at hh

def addressRegistration : Registration addressArena (type_of% @address_prefix) where
  actual := addressActual
  bridge := Iff.rfl
  variation := ⟨@address_prefix, addressRejected, address_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨addressRejected, ?_, rfl, address_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨[Label.L0, Label.L3], []⟩, 0, 1, ?_⟩
    simp [addressActual, realize, address]

def address_prefix_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.address_prefix)
      (type_of% (realize.{0,0,0,0,0} addressSignature
        (fun _ q p => address (q.1 ++ q.2) p) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.address_prefix_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.addressRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨addressArena⟩
  objectArena := .source ⟨addressArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source addressArena ⟨addressRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} addressSignature
    (fun _ q p => address (q.1 ++ q.2) p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms addressRegistration
#print axioms address_prefix_registration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
