import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.SeedQueueInvariant
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.SeedQueueInvariant

namespace Reg.D5.S3.Combinatorics.Circle.SeedQueueInvariant
universe u
noncomputable section
abbrev signature : Signature where
  Params := ℤ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ B h => B + h) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ B h => B + h + 1) (fun e => nomatch e)

/-- Only the peak readout in the first-omission inequality varies. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} (f : α → ℤ)
    (old small : List α) (mu D a b p B C : ℤ)
    (hold : Ancestors f mu D 0 old) (hdyadic : Dyadic f a small)
    (hbirth : small ≠ [] → 0 ≤ a - mu - (old.map f).sum ∧
      a - mu - (old.map f).sum ≤ D)
    (hbudget : mu ≤ b)
    (htransport : (small.map f).sum - (B - p) = b - a)
    (hcapacity : 2 * (C - B) = b - 1),
    let q := (splitBudget f (b - mu) (old ++ small)).1
    let e := (splitBudget f (b - mu) (old ++ small)).2
    let h := b - mu - (q.map f).sum
    old ++ small = q ++ e ∧ Ancestors f mu D 0 q ∧ 0 ≤ h ∧
      (a - mu - (old.map f).sum) + (e.map f).sum + p - B = h ∧
      (∀ x xs, e = x :: xs → h < f x ∧ R.readout () B h ≤ C + D / 2) ∧
      (e = [] → B + h = a - mu - (old.map f).sum + p) ∧
      (b = mu → (∀ x ∈ old ++ small, 0 < f x) → q = [] ∧ h = 0)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hall
  let x : ULift.{u} Unit := ULift.up ()
  have hr := hall (fun _ : ULift.{u} Unit => (1 : ℤ)) [] [x]
    1 0 1 1 2 3 3 (by trivial) (by simp [Dyadic])
    (by intro _; norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb := hr.2.2.2.2.1 x [] (by norm_num [splitBudget])
  norm_num [rejected, realize, splitBudget] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena.{u} (type_of% (@deferred_prefix_invariant.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deferred_prefix_invariant.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@deferred_prefix_invariant.{u}) (type_of% actual) Nat Unit where
  unitName := `D5.S3.Combinatorics.Circle.SeedQueueInvariant.deferred_prefix_invariant.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.SeedQueueInvariant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ B h => B + h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.SeedQueueInvariant
    definition := none
    coordinates := #[9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Circle.SeedQueueInvariant
