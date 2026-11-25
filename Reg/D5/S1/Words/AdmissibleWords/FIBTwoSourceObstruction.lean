import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! Source observations for the shared capacity and exact five-vertex region. -/

set_option autoImplicit false

namespace Reg.D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction

open Set MeasureTheory LeanInformationAudit
open _root_.D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

noncomputable section

namespace Capacity

private abbrev Parameters := Σ Ω : Type u, Set Ω

private abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Set p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Set p.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u} :=
  realize signature (fun _ p W => W \ p.2) (fun a => nomatch a)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => univ) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    {S H K T W : Set Ω}, μ K ≠ ⊤ →
    MeasurableSet S → MeasurableSet H → MeasurableSet T →
    S ⊆ H → S ⊆ K → T ⊆ K → W ⊆ H → W ⊆ K →
    μ.real (R.readout () ⟨Ω, S⟩ W) + μ.real (T \ H) ≤ μ.real K - μ.real S

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  letI : MeasurableSpace (ULift.{u} Unit) := ⊤
  let a : ULift.{u} Unit := ⟨()⟩
  have bad := h (Measure.dirac a) (S := ∅) (H := ∅) (K := ∅) (T := ∅) (W := ∅) (by simp)
    MeasurableSet.empty MeasurableSet.empty MeasurableSet.empty
    Subset.rfl Subset.rfl Subset.rfl Subset.rfl Subset.rfl
  have one : (Measure.dirac a).real univ = 1 := Measure.dirac_real_apply_of_mem (mem_univ a)
  norm_num [rejected, realize, one] at bad

def family : Registration arena.{u} (type_of% (@shared_capacity.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@shared_capacity.{u}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    rintro ⟨⟩
    refine ⟨⟨ULift.{u} Unit, ∅⟩, ∅, univ, ?_⟩
    simpa [actual, realize] using (empty_ne_univ : (∅ : Set (ULift.{u} Unit)) ≠ univ)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@shared_capacity.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction.shared_capacity.audit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction.Capacity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p W => W \ p.2) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Capacity

namespace Range

private abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ a b => a + b) (fun v => nomatch v)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun v => nomatch v)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q c a b : ℝ},
    ((∃ A : Fin 5 → Set ℝ, Nested A ∧
      (∀ v, MeasurableSet (A v) ∧ A v ⊆ Ico 0 1) ∧
      volume.real (A 0) = q ∧ volume.real (A 1) = q + c ∧ volume.real (A 2) = q + c ∧
      volume.real (A 3) = q ∧ volume.real (A 4) = q ∧
      volume.real (A 4 \ A 0) = a ∧ volume.real (A 3 \ A 1) = b) ↔
    0 ≤ a ∧ 0 ≤ b ∧ R.readout () a b ≤ c ∧ a ≤ q ∧ b ≤ q ∧ b ≤ 1 - (q + c))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have wrong := (h (q := 1 / 2) (c := 1 / 6) (a := 1 / 6) (b := 1 / 6)).2
    (by norm_num [rejected, realize])
  have bound := (five_vertex_range (q := 1 / 2) (c := 1 / 6) (a := 1 / 6) (b := 1 / 6)).1 wrong
  norm_num at bound

def family : Registration arena (type_of% (@five_vertex_range)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨five_vertex_range, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    rintro ⟨⟩
    refine ⟨0, 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@five_vertex_range) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction.five_vertex_range.audit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction.Range.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a b => a + b) (fun v => nomatch v))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body",
        "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Range

end

end Reg.D5.S1.Words.AdmissibleWords.FIBTwoSourceObstruction
