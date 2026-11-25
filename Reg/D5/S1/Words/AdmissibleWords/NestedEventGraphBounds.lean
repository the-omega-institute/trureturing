import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Words.AdmissibleWords.NestedEventGraphBounds

/-! A source event difference observed within the graph upper bound. -/

set_option autoImplicit false

namespace Reg.D5.S1.Words.AdmissibleWords.NestedEventGraphBounds

open Set MeasureTheory LeanInformationAudit
open _root_.D5.S1.Words.AdmissibleWords.NestedEventGraphBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

noncomputable section

private abbrev Parameters := Σ V : Type u, Σ _ : V, V → Set ℝ

private abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ p v => volume.real (p.2.2 p.2.1 \ p.2.2 v)) (fun a => nomatch a)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 2) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {G : SimpleGraph V} (q : V → ℝ) (s : V),
    (∀ v, 0 ≤ q v ∧ q v ≤ 1) → (∀ v, G.Reachable s v) →
    (∀ A : V → Set ℝ,
      (∀ v, MeasurableSet (A v) ∧ A v ⊆ Ico 0 1 ∧ volume.real (A v) = q v) →
      (∀ u v, G.Adj u v → A u ⊆ A v ∨ A v ⊆ A u) →
      ∀ v, R.readout () ⟨V, s, A⟩ v ≤ min (q s) (min (1 - q v) (distance (G := G) q s v))) ∧
    ∃ A : V → Set ℝ,
      (∀ v, MeasurableSet (A v) ∧ A v ⊆ Ico 0 1 ∧ volume.real (A v) = q v) ∧
      (∀ u v, G.Adj u v → q u ≤ q v → A u ⊆ A v) ∧
      ∀ v, volume.real (A s \ A v) = min (q s) (min (1 - q v) (distance (G := G) q s v))

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let v : ULift.{u} Unit := ⟨()⟩
  have bound := (h (G := ⊥) (fun (_ : ULift.{u} Unit) => 0) v
    (fun _ => ⟨le_rfl, zero_le_one⟩)
    (fun w => (Subsingleton.elim v w) ▸ SimpleGraph.Reachable.refl v)).1
    (fun _ => ∅) (fun _ => ⟨MeasurableSet.empty, empty_subset _, measureReal_empty⟩)
    (fun _ _ _ => Or.inl Subset.rfl) v
  exact (by norm_num : ¬ (2 : ℝ) ≤ 0) (le_trans bound (min_le_left _ _))

private def sample (x : ULift.{u} Bool) : Set ℝ :=
  if x.down then Ico 0 1 else ∅

def family : Registration arena.{u} (type_of% (@sharp_difference.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sharp_difference, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    rintro ⟨⟩
    let start : ULift.{u} Bool := ⟨true⟩
    let finish : ULift.{u} Bool := ⟨false⟩
    refine ⟨⟨ULift.{u} Bool, start, sample⟩, start, finish, ?_⟩
    norm_num [actual, realize, sample, start, finish, Real.volume_real_Ico]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sharp_difference.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.NestedEventGraphBounds.sharp_difference.audit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.NestedEventGraphBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p v => volume.real (p.2.2 p.2.1 \ p.2.2 v))
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.NestedEventGraphBounds
    definition := none
    coordinates := #[0, 3, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg",
        "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Words.AdmissibleWords.NestedEventGraphBounds

