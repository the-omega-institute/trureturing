import Reg.Support.FibonacciOriginalSourceWitness.Source84
import Reg.Support.FibonacciFactorCompletion.FixedHistoryReadouts
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

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.Injection
noncomputable section

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral

abbrev syncSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : List Label, Σ _ : Bool → List Label, Σ _ : List Label, ℕ
  State p := Fin p.2.2.2 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Label
  Anchor := Empty
  finiteAnchor := inferInstance

def syncActual : Realization syncSignature :=
  realize syncSignature
    (fun _ p z => address (synchronousPrefix p.1 p.2.1 z ++ p.2.2.1))
    (fun e => nomatch e)

def syncRejected : Realization syncSignature :=
  realize syncSignature (fun _ _ _ _ => Label.L0) (fun e => nomatch e)

abbrev syncArena : Arena.{0,0,0,0,0} where
  signature := syncSignature
  Law r := ∀ (P : List Label) (R : Bool → List Label)
    (L : ℕ) (hlen : ∀ i, (R i).length = L) (hne : R false ≠ R true)
    (w : List Label) (n : ℕ),
    Function.Injective (r.readout () ⟨P, ⟨R, ⟨w, n⟩⟩⟩)

private def twoBlocks : Bool → List Label
  | false => [Label.L0]
  | true => [Label.L2]

private theorem sync_bad : ¬ syncArena.Law syncRejected := by
  intro h
  have inj := h [] twoBlocks 1 (by intro i; cases i <;> rfl)
    (by simp [twoBlocks]) [] 1
  have eq : (fun _ : Fin 1 => false) = (fun _ : Fin 1 => true) := inj rfl
  have impossible := congrFun eq (0 : Fin 1)
  cases impossible

def syncRegistration : Registration syncArena (type_of% @synchronous_address_injective) where
  actual := syncActual
  bridge := Iff.rfl
  variation := ⟨@synchronous_address_injective, syncRejected, sync_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨syncRejected, ?_, rfl, sync_bad⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨[], ⟨twoBlocks, ⟨[], 1⟩⟩⟩,
      (fun _ : Fin 1 => false), (fun _ : Fin 1 => true), ?_⟩
    intro h
    have impossible := congrFun h 0
    change Label.L0 = Label.L2 at impossible
    cases impossible

def synchronous_address_injective_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.synchronous_address_injective)
      (type_of% (realize.{0,0,0,0,0} syncSignature
        (fun _ p z => address (synchronousPrefix p.1 p.2.1 z ++ p.2.2.1)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.Injection.sync_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.Injection.syncRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨syncArena⟩
  objectArena := .source ⟨syncArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source syncArena ⟨syncRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} syncSignature
        (fun _ p z => address (synchronousPrefix p.1 p.2.1 z ++ p.2.2.1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
    definition := none
    coordinates := #[0, 1, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


#print axioms syncRegistration
#print axioms synchronous_address_injective_registration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.Injection

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal74
noncomputable section


abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := List Label
  State := fun _ => List Label
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => List Label
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ u v => u ++ v) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => [Label.L5]) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (s e q : Guard) (u v : List Label) (hu : LegalWord s e u) (hv : LegalWord e q v), LegalWord s q (r.readout () u v)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bad := h .G0 .G0 .G0 [] [] rfl rfl
  cases bad

def evidence : Registration sourceArena (type_of% @legal_append) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@legal_append, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨[], [], [.L0], ?_⟩
    simp [actual, realize]

def legal_append_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.legal_append)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ u v => u ++ v) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal74.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal74.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ u v => u ++ v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms legal_append_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal74

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal75
noncomputable section


abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Bool → List Label
  State := fun _ => List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => List Label
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ R zs => choiceBlocks R zs) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => [Label.L5]) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (s : Guard) (R : Bool → List Label) (hR : ∀ i, LegalWord s s (R i)) (zs : List Bool), LegalWord s s (r.readout () R zs)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bad := h .G0 (fun _ => []) (fun _ => rfl) []
  cases bad

def evidence : Registration sourceArena (type_of% @choices_legal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@choices_legal, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(fun _ => [.L0]), [], [false], ?_⟩
    simp [actual, realize, choiceBlocks]

def choices_legal_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.choices_legal)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ R zs => choiceBlocks R zs) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal75.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal75.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ R zs => choiceBlocks R zs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms choices_legal_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal75

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal79
noncomputable section
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (-2 : ℝ)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (o : Ownership) (θ : ℝ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color)
    (hQ : LegalWord .G0 s Q) (hV : LegalWord s s V)
    (hQlen : Q.length = h.length) (hlen : ∀ i, V.length = (W i).length) (z : ℝ),
    (∀ n, (compose V)^[n] z ∈ CompetingT o θ s Q V h W) ↔
      InSupport s (r.readout () () z) ∧ ∀ zs : List Bool,
        BlockSupply o θ false (Q++choiceBlocks (fun _ => V) zs) (h++choiceBlocks W zs) z

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have supported : InSupport .G0 (0 : ℝ) :=
    ⟨by norm_num, (by norm_num : (0 : ℝ) ≤ 1).trans tail_arithmetic.2.2.2.2.2.le⟩
  have member : (0 : ℝ) ∈ CompetingT (fun _ => false) 0 .G0 [] [] [] (fun _ => []) := by
    refine ⟨supported, ?_, ?_⟩
    · intro p hp
      simp at hp
    · intro i p hp
      simp at hp
  have orbit : ∀ n, (compose ([] : List Label))^[n] (0 : ℝ) ∈
      CompetingT (fun _ => false) 0 .G0 [] [] [] (fun _ => []) := by
    intro n
    change ((id : ℝ → ℝ)^[n] (0 : ℝ)) ∈ _
    simpa only [Function.iterate_id, id_eq] using member
  have impossible := ((h (fun _ => false) 0 .G0 [] [] [] (fun _ => [])
    rfl rfl rfl (fun _ => rfl) 0).mp orbit).1.1
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena
    (type_of% @_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.competingT_orbit_iff_all_histories) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.competingT_orbit_iff_all_histories, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def competingT_orbit_iff_all_histories_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.competingT_orbit_iff_all_histories)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ x => x) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal79.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal79.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms competingT_orbit_iff_all_histories_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal79

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal76
noncomputable section

def fixed_finite_tail_all_histories_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.fixed_finite_tail_all_histories)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ θ => θ) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal76.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal76.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ θ => θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "body", "fn", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms fixed_finite_tail_all_histories_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal76

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal78
noncomputable section

def actual_omega_prefix_record_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.actual_omega_prefix_record)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ θ => θ) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal78.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal78.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ θ => θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_omega_prefix_record_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal78

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal80
noncomputable section

def fixed_omega_tail_all_histories_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.fixed_omega_tail_all_histories)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ θ => θ) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal80.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal80.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ θ => θ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms fixed_omega_tail_all_histories_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.ExactOriginal80

namespace Reg.Support.FibonacciOriginalSourceWitness.Source84
noncomputable section
universe u

def original_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources.original_synchronous_common_stem.{u})
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ lo => lo) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.Support.FibonacciOriginalSourceWitness.Source84.original_unit
  realizationName := `Reg.Support.FibonacciOriginalSourceWitness.Source84.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena.{u}⟩
  objectArena := .source ⟨sourceArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ lo => lo) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 25
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_registration
end
end Reg.Support.FibonacciOriginalSourceWitness.Source84
