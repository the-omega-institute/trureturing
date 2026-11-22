import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OmittedRowContraction
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ULift

/-! The residual matrix action is the observation in the pair contraction law. -/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OmittedRowContraction

open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OmittedRowContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w

noncomputable section

private abbrev Params :=
  Σ V : Type u, Σ R : Type v, Σ K : Type w, Σ _ : Field K, Σ _ : Fintype V, Matrix R V K

private abbrev signature : Signature where
  Params := Params.{u, v, w}
  State p := p.1 → p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1 → p.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{u, v, w} :=
  realize signature (fun _ p x =>
    letI := p.2.2.2.1
    letI := p.2.2.2.2.1
    p.2.2.2.2.2.mulVec x) Empty.elim

private def rejected : Realization signature.{u, v, w} :=
  realize signature (fun _ p _ =>
    letI := p.2.2.2.1
    fun _ => 1) Empty.elim

private abbrev arena : Arena where
  signature := signature.{u, v, w}
  Law T := ∀ {V : Type u} {R : Type v} {K : Type w} [k : Field K] [f : Fintype V]
    (G : SimpleGraph V) [Fintype G.ConnectedComponent] (p : V → K)
    (B : Matrix R V K) (x : V → K) (_ : ∀ v, p v ≠ 0),
    ((∀ u v, G.Adj u v → p u * x v = p v * x u) ∧ T.readout () ⟨V, R, K, k, f, B⟩ x = 0) ↔
      ∃! z : G.ConnectedComponent → K,
        (∀ v, x v = p v * z (G.connectedComponentMk v)) ∧
          (compressedRows G p B).mulVec z = 0 ∧
          ((∀ v, x v ≠ 0) ↔ ∀ c, z c ≠ 0)

private theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  classical
  let G : SimpleGraph (ULift.{u} (Fin 1)) := ⊥
  let := Fintype.ofFinite G.ConnectedComponent
  let B : Matrix (ULift.{v} (Fin 1)) (ULift.{u} (Fin 1)) (ULift.{w} ℚ) := 0
  have hp : ∀ _ : ULift.{u} (Fin 1), (1 : ULift.{w} ℚ) ≠ 0 := fun _ => one_ne_zero
  have hz := (pair_and_residual_rows_iff G 1 B 0 hp).mp ⟨by simp [G], by simp⟩
  have hbad := ((h G 1 B 0 hp).mpr hz).2
  exact one_ne_zero (congrFun hbad (ULift.up 0) : (1 : ULift.{w} ℚ) = 0)

def sourceRegistration : Registration arena.{u, v, w}
    (type_of% (@pair_and_residual_rows_iff.{u, v, w})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pair_and_residual_rows_iff.{u, v, w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let B : Matrix (ULift.{v} (Fin 1)) (ULift.{u} (Fin 1)) (ULift.{w} ℚ) := fun _ _ => 1
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (Fin 1), ULift.{w} ℚ,
      inferInstance, inferInstance, B⟩, (fun _ => 1), (fun _ => 0), ?_⟩
    intro h
    have hr := congrFun h (ULift.up 0)
    exact one_ne_zero (by simpa [actual, realize, B, Matrix.mulVec, dotProduct] using hr :
      (1 : ULift.{w} ℚ) = 0)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pair_and_residual_rows_iff.{u, v, w}) (Realization signature.{u, v, w}) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OmittedRowContraction.pair_and_residual_rows_iff.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OmittedRowContraction.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, w}⟩
  objectArena := .source ⟨arena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v, w} ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OmittedRowContraction
    definition := none
    coordinates := #[0, 1, 2, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OmittedRowContraction
