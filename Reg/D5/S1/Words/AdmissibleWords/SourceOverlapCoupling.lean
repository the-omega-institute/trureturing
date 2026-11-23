import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Words.AdmissibleWords.SourceOverlapCoupling

/-! Reading the specified overlap at the target of an event difference. -/

set_option autoImplicit false

namespace Reg.D5.S1.Words.AdmissibleWords.SourceOverlapCoupling

open Set MeasureTheory LeanInformationAudit
open _root_.D5.S1.Words.AdmissibleWords.SourceOverlapCoupling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

noncomputable section

private abbrev Parameters := Σ V : Type u, V → ℝ

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
  realize signature (fun _ p v => p.2 v) (fun a => nomatch a)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature.{u}
  Law F := ∀ {V : Type u} (R : V → V → Prop) (q overlap : V → ℝ) (s : V),
    q s ∈ Icc 0 1 → overlap s = q s →
    (∀ v, overlap v ∈ Icc 0 (q s)) →
    (∀ v, q v - overlap v ∈ Icc 0 (1 - q s)) →
    (∀ ⦃u v⦄, R u v → overlap u ≤ overlap v ∧ q u - overlap u ≤ q v - overlap v) →
    ∃ A : V → Set ℝ,
      (∀ v, MeasurableSet (A v) ∧ A v ⊆ Ico 0 1 ∧ volume.real (A v) = q v) ∧
      (∀ ⦃u v⦄, R u v → A u ⊆ A v) ∧
      ∀ v, volume.real (A s \ A v) = q s - F.readout () ⟨V, overlap⟩ v

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let s : ULift.{u} Unit := ⟨()⟩
  obtain ⟨A, _, _, difference⟩ :=
    h (fun _ _ => False) (fun _ => 0) (fun _ => 0) s (by norm_num) rfl
      (by intro v; norm_num) (by intro v; norm_num) (by intro _ _ contra; exact contra.elim)
  have bad := difference s
  simp [rejected, realize] at bad

def family : Registration arena.{u} (type_of% (@exists_nested_events.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_nested_events, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    rintro ⟨⟩
    let overlap (v : ULift.{u} Bool) : ℝ := if v.down then 1 else 0
    refine ⟨⟨ULift.{u} Bool, overlap⟩, ⟨true⟩, ⟨false⟩, ?_⟩
    simp [actual, realize, overlap]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_nested_events.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.SourceOverlapCoupling.exists_nested_events.audit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.SourceOverlapCoupling.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p v => p.2 v) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.SourceOverlapCoupling
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "arg", "body", "arg", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Words.AdmissibleWords.SourceOverlapCoupling

