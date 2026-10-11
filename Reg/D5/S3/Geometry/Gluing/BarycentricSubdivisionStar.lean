import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.BarycentricSubdivisionStar
import Reg.Support.DependentFamily

open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Gluing.BarycentricSubdivisionStar
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.Gluing.BarycentricSubdivisionStar
noncomputable section
universe u
set_option maxHeartbeats 800000

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 4 → ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ β => β 0) (fun e => nomatch e)

def intervened (i : Bool) : Realization signature :=
  realize signature (fun j _ β => if j = i then -1 else β 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Fin 4 → E), AffineIndependent ℝ p →
    ∀ (β : Fin 4 → ℝ), (∀ j, 0 ≤ β j) → (∑ j, β j = 1) →
    ∀ (x : E), x = ∑ j, β j • p j →
    (x ∈ closedStar p ↔ ∀ j ≠ 0, β j ≤ R.readout false () β) ∧
    (x ∈ openStar p ↔ ∀ j ≠ 0, β j < R.readout true () β)

-- The intervention keeps the full source family and changes only its distinguished coordinate readout.
theorem intervened_law (i : Bool) : ¬ arena.{u}.Law (intervened i) := by
  intro h
  let p : Fin 4 → ULift.{u} (Fin 4 → ℝ) := fun i => ULift.up ((Pi.basisFun ℝ (Fin 4)) i)
  have hp : AffineIndependent ℝ p := by
    let e : ULift.{u} (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) := ULift.moduleEquiv
    exact ((Pi.basisFun ℝ (Fin 4)).linearIndependent.affineIndependent).map'
      e.symm.toAffineEquiv.toAffineMap e.symm.injective
  let β : Fin 4 → ℝ := ![1,0,0,0]
  have hn : ∀ j, 0 ≤ β j := by intro j; fin_cases j <;> norm_num [β]
  have hs : ∑ j, β j = 1 := by norm_num [β, Fin.sum_univ_succ]
  have ht := actual_closed_and_open_star_iff p hp β hn hs _ rfl
  have ho := ht.2.mpr (by intro j hj; fin_cases j <;> norm_num [β] at *)
  have hc := ht.1.mpr (by intro j hj; fin_cases j <;> norm_num [β] at *)
  have hh := h p hp β hn hs _ rfl
  cases i
  · have hz := hh.1.mp hc 1 (by decide)
    norm_num [intervened, realize, β] at hz
  · have hz := hh.2.mp ho 1 (by decide)
    norm_num [intervened, realize, β] at hz

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro E _ _ p hp β hn hs x hx
    exact actual_closed_and_open_star_iff p hp β hn hs x hx,
    intervened false, intervened_law false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervened i, ?_, rfl, intervened_law i⟩
      intro j h
      funext a β
      simp [actual, intervened, realize, h]
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
    norm_num [actual, realize]

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.Gluing.BarycentricSubdivisionStar.actual_closed_and_open_star_iff.{u})
    (type_of% (realize signature (fun _ _ β => β 0) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.BarycentricSubdivisionStar.actual_closed_and_open_star_iff.distinguishedCoordinate
  realizationName := `Reg.D5.S3.Geometry.Gluing.BarycentricSubdivisionStar.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ β => β 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.BarycentricSubdivisionStar
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
          "fn", "arg", "arg", "body", "body", "arg"]
        stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
          "arg", "arg", "body", "body", "arg"]
        stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]
}

#print axioms registration
end
end Reg.D5.S3.Geometry.Gluing.BarycentricSubdivisionStar
