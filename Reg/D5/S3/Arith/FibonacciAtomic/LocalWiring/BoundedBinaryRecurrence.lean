import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrence
import Reg.Support.DependentFamily

/-! Genuine future digits of the executable generator, varying the observed word. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrence

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrence
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.PublicRowSeedReadiness (bitNat rowStream seedFromPrefix)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : Nat, Nat
  State _ := List Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p word => generated p.1 word p.2) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ d : Nat,
    (∀ (word : List Bool) (i : Nat) (s : Nat → Bool), Legal d s →
      word = observed (2*d) s → F.readout () ⟨d, i⟩ word = some (s i)) ∧
    (∀ s t : Nat → Bool, Legal d s → Legal d t →
      observed (2*d) s = observed (2*d) t → ∀ i, s i = t i) ∧
    (∀ (word : List Bool) (s : Nat → Bool), Legal d s → word = observed (2*d) s →
      ∃ c, synthesize d word = some c ∧ (∀ i, rowStream c (seedFromPrefix word) i = s i) ∧
        ∃ earlier later, masks d = earlier ++ c :: later ∧ ∀ b ∈ earlier,
          observed (2*d) (rowStream b (seedFromPrefix word)) ≠ word) ∧
    (masks d).length = 2^d ∧
    (d = 0 → ∀ i, generated d [] i = some false)

private def impulse (i : Nat) : Bool := decide (i = 0)

private theorem impulse_legal : Legal 1 impulse :=
  ⟨1, Nat.le_refl _, fun _ => false, by intro i; simp [bitNat, impulse]⟩

private theorem constant_legal : Legal 1 (fun _ => true) :=
  ⟨1, Nat.le_refl _, fun _ => true, by intro i; simp [bitNat]⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 1).1 [true, false] 4 impulse impulse_legal rfl
  change (none : Option Bool) = some false at bad
  cases bad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨1, 4⟩, [true, false], [true, true], ?_⟩
  change generated 1 [true, false] 4 ≠ generated 1 [true, true] 4
  have good := (bounded_binary_recurrence 1).1
  rw [good [true, false] 4 impulse impulse_legal rfl,
      good [true, true] 4 (fun _ => true) constant_legal rfl]
  decide

def family : Registration arena (type_of% bounded_binary_recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bounded_binary_recurrence, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bounded_binary_recurrence) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrence.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrence.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrence
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.BoundedBinaryRecurrence
