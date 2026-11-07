import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.ActualOutputClosedGraph
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.ActualOutputClosedGraph
open LeanInformationAudit
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.ActualOutputClosedGraph

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

/-- The complete original telescope, with only the joint norm comparison observed. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Set (E →L[ℝ] ℝ)) (S : E →L[ℝ] E →L[ℝ] E) (D : E → E → E)
    (hsep : ∀ x y : E, (∀ α : P, α.val x = α.val y) → x = y)
    (hs : ∀ a b, S a b = S b a)
    (hconj : ∀ (α : P) (a b : E),
      (α.val (S b a) : ℂ) - Complex.I * (α.val (D b a) : ℂ) =
        star ((α.val (S a b) : ℂ) - Complex.I * (α.val (D a b) : ℂ)))
    (hassoc : ∀ a b c, S (S a b) c - S a (S b c) = D (D a b) c - D a (D b c))
    (hr : UniformActualReadback P D),
    ∃ B : E →L[ℝ] E →L[ℝ] E, (∀ a b, B a b = D a b) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ a b, R.readout () () ‖D a b‖ (K * ‖a‖ * ‖b‖)

private theorem actual_law : arena.{u}.Law actual := @raw_relation_bounded_bilinear.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let E := PUnit.{u+1}
  let P : Set (E →L[ℝ] ℝ) := Set.univ
  let S : E →L[ℝ] E →L[ℝ] E := 0
  let D : E → E → E := fun _ _ => 0
  have hr : UniformActualReadback P D := by
    intro α η _
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_⟩
    · intro j
      exact Fin.elim0 j
    · rintro p ⟨⟨a,b⟩,rfl⟩
      simp [D]
  obtain ⟨B, hB, K, hK, hb⟩ := h P S D
    (fun x y _ => Subsingleton.elim x y)
    (by intro a b; simp [S])
    (by intro α a b; simp [S, D])
    (by intro a b c; simp [S, D]) hr
  exact hb 0 0

def family : Registration arena.{u}
    (type_of% (@raw_relation_bounded_bilinear.{u})) where
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
    (@raw_relation_bounded_bilinear.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.ActualOutputClosedGraph.rawRelationUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.ActualOutputClosedGraph.family
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
    owner := `D5.S3.Quantum.Analysis.ActualOutputClosedGraph
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "arg", "arg", "body",
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
end Reg.D5.S3.Quantum.Analysis.ActualOutputClosedGraph

end
