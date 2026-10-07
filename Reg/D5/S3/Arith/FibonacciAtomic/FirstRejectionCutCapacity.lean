import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

open _root_.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity

abbrev signature : Signature where
  Params := Σ k : ℕ, Finset (Fin (k+1))
  State p := Word p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Label p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => task w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊤) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (A : Finset (Fin (k+1))),
    (∀ P : Profile k A, code A (representative P) = encode P) ∧
    (∀ a : Side k A, ∃ P : Profile k A, code A a = encode P) ∧
    (∀ a a' : Side k A,
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response (fun _ : Fin (k+1) => Window)
        (R.readout () ⟨k,A⟩) (fun r => r ∈ A) a =
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.response (fun _ : Fin (k+1) => Window)
        (R.readout () ⟨k,A⟩) (fun r => r ∈ A) a' ↔ code A a = code A a') ∧
    delta A ≤ d A ∧
    D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity (fun _ : Fin (k+1) => Window)
      (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 2 ^ d A + (∑ j ∈ internals A, 2 ^ c A j) +
        (if Fin.last k ∈ A then 2 ^ (d A - delta A) else 0) ∧
    (∀ w : Word k, boolean w = decide ((R.readout () ⟨k,A⟩) w = ⊤)) ∧
    (∀ a : Side k A,
      (∀ b, boolean (merge A a b) = false) ↔ closed A a ≠ ⊤) ∧
    (∀ a a' : Side k A,
      (∀ b, boolean (merge A a b) = boolean (merge A a' b)) ↔
        (closed A a ≠ ⊤ ∧ closed A a' ≠ ⊤) ∨
        (closed A a = ⊤ ∧ closed A a' = ⊤ ∧ ∀ i, Cross A i → port A a i = port A a' i)) ∧
    D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity (fun _ : Fin (k+1) => Window)
      boolean (fun r => r ∈ A) = 2 ^ d A + epsilon A ∧
    (A = ∅ → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
      (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 1) ∧
    (A = Finset.univ → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
      (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = k+2) ∧
    (∀ m : ℕ, 1 ≤ m → m < k+1 → A = interval k 0 m →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = m+1) ∧
    (1 ≤ k → A = {Fin.last k} → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
      (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 3) ∧
    (∀ l : ℕ, 0 < l → l < k → A = interval k l (k+1) →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 2*(k+1-l)+2) ∧
    (∀ l r : ℕ, 0 < l → l < r → r < k+1 → A = interval k l r →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 2*(r-l)+2) ∧
    (A = {(0 : Fin (k+1))} → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
      (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 2) ∧
    (∀ i : Fin (k+1), 0 < i.val → i.val < k → A = {i} →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 4) ∧
    (∀ l r : ℕ, 0 < l → l+1 < r → r ≤ k+1 → A = interval k l r →
      D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 2*(r-l)+2) ∧
    (k = 0 → (A = ∅ → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 1) ∧
      (A = Finset.univ → D5.S3.Observer.Separation.SurjectiveColumnSharpWidth.capacity
        (fun _ : Fin (k+1) => Window) (R.readout () ⟨k,A⟩) (fun r => r ∈ A) = 2)) ∧
    (1 ≤ k →
      List.ofFn (x k) = .high :: .low :: List.replicate (k-1) .middle ∧
      List.ofFn (y k) = List.replicate k .middle ++ [.zero] ∧
      boolean (x k) = false ∧ boolean (y k) = false ∧
      (R.readout () ⟨k,A⟩) (x k) = ((0 : Fin (k+1)) : Label k) ∧
      (R.readout () ⟨k,A⟩) (y k) = (Fin.last k : Label k) ∧
      ¬ ∃ post : Bool → Label k, ∀ w : Word k, post (boolean w) = (R.readout () ⟨k,A⟩) w)

theorem actual_law : arena.Law actual := by
  intro k A
  exact result k A

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 0 ∅).2.2.2.2.2.1 (fun _ => Window.zero)
  change false = decide ((⊤ : Label 0) = ⊤) at bad
  simp at bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨0,∅⟩, (fun _ => Window.zero), (fun _ => Window.middle), ?_⟩
    change task (fun _ : Fin 1 => Window.zero) ≠ task (fun _ : Fin 1 => Window.middle)
    simp [task,bad]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ w => task w) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "FirstRejectionCutCapacity") "result") "Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity/Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ w => task w) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxRecDepth, value := .nat 4096 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"FirstRejectionCutCapacity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"FirstRejectionCutCapacity\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"FirstRejectionCutCapacity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"FirstRejectionCutCapacity\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.arena) (Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration).actual

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"FirstRejectionCutCapacity\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"FirstRejectionCutCapacity\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration).bridge

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.observation0 : (k : Nat) →
  (A :
      Finset.{0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
    (a a' : D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.Side k A) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.signature
          (@Sigma.mk.{0, 0} Nat
            (fun (k : Nat) =>
              Finset.{0}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            k A) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.signature PUnit.unit.{1}
          (@Sigma.mk.{0, 0} Nat
            (fun (k : Nat) =>
              Finset.{0}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            k A) :=
  fun (k : Nat)
    (A :
      Finset.{0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (a a' : D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.Side k A) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.signature
    Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (k : Nat) =>
        Finset.{0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      k A)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"FirstRejectionCutCapacity\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"function\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"FirstRejectionCutCapacity\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.result, part := .type, path := [.body, .body, .argument, .argument, .function, .argument, .body, .body, .function, .argument, .function, .argument, .function, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"FirstRejectionCutCapacity\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"FirstRejectionCutCapacity\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"FirstRejectionCutCapacity\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"FirstRejectionCutCapacity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"FirstRejectionCutCapacity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
