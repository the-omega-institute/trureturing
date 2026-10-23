import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.CycleDiagonalUnitPropagation
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.Walks.CycleDiagonalUnitPropagation
open _root_.D5.S3.Combinatorics.Graph.Walks.CycleDiagonalUnitPropagation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The complex potential operand in the original joint-commutant clause. -/
abbrev signature : Signature where
  Params := ℕ
  State L := Fin L → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ L := Matrix (Fin L) (Fin L) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ v => (Matrix.diagonal v).map Complex.ofReal) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

/-- All hypotheses and conclusions remain; only the selected complex operand varies. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (L : ℕ) (hL : 3 ≤ L) (v : Fin L → ℝ)
    (hseed : ∃ j : Fin L,
      Matrix.single j j (1 : ℝ) ∈ Algebra.adjoin ℝ
        {(SimpleGraph.cycleGraph L).lapMatrix ℝ, Matrix.diagonal v} ∧
      Matrix.single (j + ⟨1, by omega⟩) (j + ⟨1, by omega⟩) (1 : ℝ) ∈ Algebra.adjoin ℝ
        {(SimpleGraph.cycleGraph L).lapMatrix ℝ, Matrix.diagonal v}),
    Algebra.adjoin ℝ {(SimpleGraph.cycleGraph L).lapMatrix ℝ, Matrix.diagonal v} = ⊤ ∧
    (∀ X : Matrix (Fin L) (Fin L) ℂ,
      Commute X (((SimpleGraph.cycleGraph L).lapMatrix ℝ).map Complex.ofReal) →
      Commute X (R.readout () L v) →
      ∃ c : ℂ, X = c • (1 : Matrix (Fin L) (Fin L) ℂ)) ∧
    (∀ O : Matrix (Fin L) (Fin L) ℝ,
      O ∈ Matrix.orthogonalGroup (Fin L) ℝ →
      Commute O ((SimpleGraph.cycleGraph L).lapMatrix ℝ) →
      Commute O (Matrix.diagonal v) → O = 1 ∨ O = -1)

/-- A genuine seed instance makes the rejected whole-family Law falsifiable. -/
private theorem rejected_fails : ¬ arena.Law rejected := by
  classical
  let v : Fin 3 → ℝ := fun i => i.val
  let V : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal v
  let B := Algebra.adjoin ℝ {(SimpleGraph.cycleGraph 3).lapMatrix ℝ, V}
  have hV : V ∈ B := Algebra.subset_adjoin (by simp)
  have hVV : V * V ∈ B := B.mul_mem hV hV
  have h1 : Matrix.single (1 : Fin 3) 1 (1 : ℝ) ∈ B := by
    have hm := B.sub_mem (B.smul_mem hV (2 : ℝ)) hVV
    convert hm using 1
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [V, v, Matrix.diagonal, Matrix.single, Matrix.mul_apply,
        Fin.sum_univ_three, Matrix.smul_apply]
  have h2 : Matrix.single (2 : Fin 3) 2 (1 : ℝ) ∈ B := by
    have hm := B.smul_mem (B.sub_mem hVV hV) (1 / 2 : ℝ)
    convert hm using 1
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [V, v, Matrix.diagonal, Matrix.single, Matrix.mul_apply,
        Fin.sum_univ_three, Matrix.smul_apply]
    all_goals decide
  have hs : ∃ j : Fin 3,
      Matrix.single j j (1 : ℝ) ∈ B ∧
      Matrix.single (j + ⟨1, by omega⟩) (j + ⟨1, by omega⟩) (1 : ℝ) ∈ B := by
    refine ⟨1, h1, ?_⟩
    have hidx : (1 : Fin 3) + (⟨1, by omega⟩ : Fin 3) = 2 := by decide
    simpa only [hidx] using h2
  intro h
  let X := ((SimpleGraph.cycleGraph 3).lapMatrix ℝ).map Complex.ofReal
  have hc := (h 3 (by omega) v hs).2.1 X (Commute.refl X)
    (show Commute X (rejected.readout () 3 v) from Commute.zero_right X)
  obtain ⟨c, he⟩ := hc
  have hab := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 1) he
  norm_num [X, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_three_eq_top,
    Matrix.diagonal, Matrix.one_apply, Matrix.smul_apply] at hab

def source_registration : Registration arena (type_of% @cycle_diagonal_units_full) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cycle_diagonal_units_full, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨3, (fun _ => 0), (fun _ => 1), ?_⟩
    intro he
    have hd := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) he
    change (0 : ℂ) = 1 at hd
    exact zero_ne_one hd

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@cycle_diagonal_units_full) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.CycleDiagonalUnitPropagation.unit
  realizationName := Lean.Name.str
    `Reg.D5.S3.Combinatorics.Graph.Walks.CycleDiagonalUnitPropagation "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ v => (Matrix.diagonal v).map Complex.ofReal) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.CycleDiagonalUnitPropagation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg",
        "body", "body", "domain", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms cycle_diagonal_units_full
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.Graph.Walks.CycleDiagonalUnitPropagation
