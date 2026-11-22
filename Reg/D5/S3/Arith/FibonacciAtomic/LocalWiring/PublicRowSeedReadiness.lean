import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.PublicRowSeedReadiness
import Reg.Support.DependentFamily

/-! The actual next-cut presence for a fixed public recurrence row. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.PublicRowSeedReadiness

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.OrderedBirthPrefix
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.PublicRowSeedReadiness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

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
  realize signature (fun _ p t => present t p) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (r : Nat) (c seed : Fin r → Bool) (n : Nat) (_hn : 2 ≤ n),
    (r ≤ matureSize n ↔ ∀ b : Fin r → Bool, compatibleSeeds c seed b n → ∀ p : Address,
      F.readout () p (rowTree c seed (n+1)) = present (rowTree c b (n+1)) p) ∧
    (r ≤ matureSize n ↔ ∀ b : Fin r → Bool, compatibleSeeds c seed b n →
       rowTree c seed n = rowTree c b n) ∧
    (r ≤ matureSize n ↔ ∀ b : Fin r → Bool, compatibleSeeds c seed b n →
      (∀ as : List Action, eval (birthStream c seed) n as = eval (birthStream c b) n as) ∧
      (∀ (policy : List Reply → Option Action) (fuel : Nat) (hist : List Reply),
        adaptiveEval policy (birthStream c seed) fuel n hist =
        adaptiveEval policy (birthStream c b) fuel n hist)) ∧
    matureSize n = Nat.fib n - 1 ∧
    maturePrefix (shape (rowTree c seed n)) =
      some (n, prefixBits (birthStream c seed) (matureSize n)) ∧
    (r ≤ matureSize n →
      installRow c (shape (rowTree c seed n)) = some (n, birthStream c seed) ∧
      (shapeFromIncidence (incidenceAddresses (shape (rowTree c seed n)))).bind (installRow c) =
        some (n, birthStream c seed) ∧
      (shapeFromFrontier (frontierAddresses (shape (rowTree c seed n)))).bind (installRow c) =
        some (n, birthStream c seed)) ∧
    (∀ j : Fin r, rowStream c seed j.val = seed j) ∧
    (∀ i : Nat, rowStream c seed (i+r) =
      (List.ofFn (fun j : Fin r => c j && rowStream c seed (i+j.val))).foldl Bool.xor false) ∧
    (∀ i : Nat, bitNat (rowStream c seed (i+r)) =
      (∑ j : Fin r, bitNat (c j) * bitNat (rowStream c seed (i+j.val))) % 2) ∧
    (∀ s : Nat → Bool, (∀ j : Fin r, s j.val = seed j) →
      (∀ i : Nat, s (i+r) = (List.ofFn (fun j : Fin r => c j && s (i+j.val))).foldl Bool.xor false) →
      s = rowStream c seed) ∧
    (r = 0 → ∀ i, rowStream c seed i = false) ∧
    Step (rowTree c seed n) (rowTree c seed (n+1)) ∧
    reply (birthStream c seed) n .update = .ack

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let c : Fin 0 → Bool := fun j => Fin.elim0 j
  have h0 := (h 0 c c 2 (by decide)).1.mp (Nat.zero_le _)
  have bad := h0 c rfl []
  change false = present (rowTree c c 3) [] at bad
  have hh : present (rowTree c c 3) [] = true := by simp [present, atTree]
  rw [hh] at bad
  cases bad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  let c : Fin 1 → Bool := fun _ => false
  refine ⟨[false, false], rowTree c (fun _ => true) 3, rowTree c (fun _ => false) 3, ?_⟩
  change present (rowTree c (fun _ => true) 3) [false, false] ≠
    present (rowTree c (fun _ => false) 3) [false, false]
  have ini (v : Bool) : consume (birthStream c (fun _ => v)) 0 = v := by
    change rowStream c (fun _ => v) 0 = v
    rw [rowStream, dite_eq_left (by decide)]
  have next (v : Bool) : consume (birthStream c (fun _ => v)) 1 = false := by
    change rowStream c (fun _ => v) 1 = false
    rw [rowStream, dite_eq_right (by decide)]
    simp [c]
  simp [rowTree, physicalBirthClock, birthRound, ini, next, present, atTree]

def family : Registration arena (type_of% public_row_seed_readiness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨public_row_seed_readiness, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@public_row_seed_readiness) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.PublicRowSeedReadiness.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.PublicRowSeedReadiness.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.PublicRowSeedReadiness
    definition := none
    coordinates := #[7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.PublicRowSeedReadiness
