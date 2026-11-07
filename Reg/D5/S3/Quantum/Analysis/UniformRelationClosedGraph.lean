import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.UniformRelationClosedGraph
import Reg.Support.DependentFamily

/-! Source-bound comparison readout for the full uniform relation theorem. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.UniformRelationClosedGraph
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.UniformRelationClosedGraph

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Set (E →L[ℝ] ℝ)) (S : E →L[ℝ] E →L[ℝ] E) (D : E → E → E),
    (∀ x : E, (∀ α ∈ P, α x = 0) → x = 0) →
    (∀ a b, S a b = S b a) →
    (∀ α ∈ P, ∀ a b : E,
      (α (S b a) : ℂ) - Complex.I * (α (D b a) : ℂ) =
        star ((α (S a b) : ℂ) - Complex.I * (α (D a b) : ℂ))) →
    (∀ a b c, S (S a b) c - S a (S b c) =
      D (D a b) c - D a (D b c)) → UniformReadout P D →
    ∃ B : E →L[ℝ] E →L[ℝ] E, (∀ a b, B a b = D a b) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ a b, R.readout () () ‖D a b‖ (K * ‖a‖ * ‖b‖)

private theorem actual_law : arena.{u}.Law actual := @bilinear_bounded.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hs : ∀ x : PUnit.{u+1},
      (∀ α ∈ (∅ : Set (PUnit.{u+1} →L[ℝ] ℝ)), α x = 0) → x = 0 := by
    intro x hx
    exact Subsingleton.elim _ _
  have hc : ∀ α ∈ (∅ : Set (PUnit.{u+1} →L[ℝ] ℝ)), ∀ a b : PUnit.{u+1},
      (α ((0 : PUnit.{u+1} →L[ℝ] PUnit.{u+1} →L[ℝ] PUnit.{u+1}) b a) : ℂ) -
          Complex.I * (α ((fun _ _ => 0) b a) : ℂ) =
        star ((α ((0 : PUnit.{u+1} →L[ℝ] PUnit.{u+1} →L[ℝ] PUnit.{u+1}) a b) : ℂ) -
          Complex.I * (α ((fun _ _ => 0) a b) : ℂ)) := by
    intro α hα
    exact (Set.notMem_empty α hα).elim
  have hr : UniformReadout (∅ : Set (PUnit.{u+1} →L[ℝ] ℝ)) (fun _ _ => 0) := by
    intro α hα
    exact (Set.notMem_empty α hα).elim
  obtain ⟨B,hB,K,hK,hb⟩ := h (E := PUnit.{u+1}) ∅ 0 (fun _ _ => 0)
    hs (by intros; rfl) hc (by intros; simp) hr
  exact hb 0 0

def family : Registration arena.{u} (type_of% (@bilinear_bounded.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hb : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bilinear_bounded.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.UniformRelationClosedGraph.bilinearBoundedUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.UniformRelationClosedGraph.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.UniformRelationClosedGraph
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg", "body", "arg", "arg", "body",
        "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Quantum.Analysis.UniformRelationClosedGraph
