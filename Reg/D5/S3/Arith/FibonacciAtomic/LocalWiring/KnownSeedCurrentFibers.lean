import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
import Reg.Support.DependentFamily

/-! The actual presence reply distinguishes both choices of a current physical cherry. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Address
  State _ := Labelled
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p t => nextPresence t p) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (n : Nat) (s : Shape) (_hn : 2 ≤ n) (_hs : s ∈ rankedShapes n),
    (∀ t, t ∈ rankedTrees n ↔ After n t) ∧
    (∀ u, u ∈ rankedShapes n ↔ ∃ t, After n t ∧ shape t = u) ∧
    (∀ t, t ∈ currentFiber n s ↔ After n t ∧ shape t = s) ∧
    (∀ p, p ∈ cherries s ↔ atTree s p = some cherry) ∧
    Function.Bijective (fiberBits n s) ∧
    (cherries s).card = Nat.fib (n - 1) ∧
    (currentFiber n s).card = 2 ^ Nat.fib (n - 1) ∧
    (rankedShapes n).card = 2 ^ (Nat.fib n - 1) ∧
    (rankedTrees n).card = 2 ^ (Nat.fib (n + 1) - 1) ∧
    (∀ t w p, t ∈ currentFiber n s → Step t w → F.readout () p t = present w p) ∧
    (∀ t p, t ∈ currentFiber n s → (nextPresence t p = true ↔ present s p = true ∨
        ∃ q : Address, ∃ b : Bool, isBeta t q = true ∧ p = q ++ [b])) ∧
    (∀ (t : ↥(currentFiber n s)) (p : ↥(cherries s)),
      nextPresence t.1 (p.1 ++ [false, false]) = fiberBits n s t p) ∧
    Function.Injective (fun t : ↥(currentFiber n s) => nextPresence t.1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : cherry ∈ rankedShapes 2 := by decide
  have ht : FreeMagma.mul beta alpha ∈ currentFiber 2 cherry := by decide
  obtain ⟨_, _, _, _, _, _, _, _, _, advance, _, _, _⟩ := h 2 cherry (by decide) hs
  have eq := advance (.mul beta alpha) (.mul (.mul beta alpha) beta)
    [false, false] ht (.branch .betaLeft .alphaToBeta)
  cases eq

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨[false, false], .mul beta alpha, .mul alpha beta, ?_⟩
  intro h
  cases h

def family : Registration arena (type_of% exact_known_seed_fibres) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_known_seed_fibres, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    exact_known_seed_fibres (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
    definition := none
    coordinates := #[6]
    readouts := #[{
      path := #["body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg",
        "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
