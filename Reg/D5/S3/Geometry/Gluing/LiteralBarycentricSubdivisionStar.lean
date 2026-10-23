import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.LiteralBarycentricSubdivisionStar
import Reg.Support.DependentFamily

open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Gluing.BarycentricSubdivisionStar
open _root_.D5.S3.Geometry.Gluing.LiteralBarycentricSubdivisionStar
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.Gluing.LiteralBarycentricSubdivisionStar.LiteralSecond
noncomputable section
universe u
set_option maxHeartbeats 800000

abbrev signature : Signature where
  Params := Unit
  State _ := Equiv.Perm (Fin 4)
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 4
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ π => π 0) (fun e => nomatch e)

def intervened (selected : Bool) : Realization signature :=
  realize signature (fun role _ π => if role = selected then 1 else π 0)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Fin 4 → E), AffineIndependent ℝ p → ∀ (i : Fin 4) (x : E),
      (x ∈ literalClosedStar p i ↔ ∃ π : Equiv.Perm (Fin 4),
        R.readout false () π = i ∧ x ∈ closedStar (fun k => barycenter p (prefixFace π k))) ∧
      (x ∈ literalOpenStar p i ↔ ∃ π : Equiv.Perm (Fin 4),
        R.readout true () π = i ∧ x ∈ openStar (fun k => barycenter p (prefixFace π k)))

private theorem singleton_in_both {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Fin 4 → E) :
    p 0 ∈ literalClosedStar p 0 ∧ p 0 ∈ literalOpenStar p 0 := by
  classical
  let D : SecondFaceChain := {
    chains := {{{0}}}
    nonempty := by simp
    chain_nonempty := by simp
    face_nonempty := by simp
    first_comparable := by simp
    comparable := by simp }
  have hv : secondBarycenter p '' (D.chains : Set _) = {p 0} := by
    simp [D, secondBarycenter, barycenter]
  have hh : secondHull p D = {p 0} := by
    rw [secondHull, hv, convexHull_singleton]
  constructor
  · exact ⟨D, by simp [hv], by simp [hh]⟩
  · exact ⟨D, by simp [hv], by simp [hh]⟩

theorem intervened_law (selected : Bool) : ¬ arena.{u}.Law (intervened selected) := by
  intro h
  let p : Fin 4 → ULift.{u} (Fin 4 → ℝ) :=
    fun i => ULift.up ((Pi.basisFun ℝ (Fin 4)) i)
  have hp : AffineIndependent ℝ p := by
    let e : ULift.{u} (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) := ULift.moduleEquiv
    exact ((Pi.basisFun ℝ (Fin 4)).linearIndependent.affineIndependent).map'
      e.symm.toAffineEquiv.toAffineMap e.symm.injective
  have hs := singleton_in_both p
  have hh := h p hp 0 (p 0)
  cases selected
  · obtain ⟨π, hπ, _⟩ := hh.1.mp hs.1
    simpa [intervened, realize] using hπ
  · obtain ⟨π, hπ, _⟩ := hh.2.mp hs.2
    simpa [intervened, realize] using hπ

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro E _ _ p hp i x
    exact literal_second_closed_and_open_star_iff p hp i x,
    intervened false, intervened_law false⟩
  sensitivity := by
    constructor
    · intro selected
      refine ⟨intervened selected, ?_, rfl, intervened_law selected⟩
      intro role h
      funext i π
      simp [actual, intervened, realize, h]
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨(), Equiv.refl _, Equiv.swap 0 1, ?_⟩
    change (Equiv.refl (Fin 4)) 0 ≠ (Equiv.swap (0 : Fin 4) 1) 0
    simp only [Equiv.refl_apply, Equiv.swap_apply_left]
    norm_num

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.Gluing.LiteralBarycentricSubdivisionStar.literal_second_closed_and_open_star_iff.{u})
    (type_of% (realize signature (fun _ _ π => π 0) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.LiteralBarycentricSubdivisionStar.literal_second_closed_and_open_star_iff.parentFlagIncidence
  realizationName := `Reg.D5.S3.Geometry.Gluing.LiteralBarycentricSubdivisionStar.LiteralSecond.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ π => π 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.LiteralBarycentricSubdivisionStar
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "body", "fn", "arg", "fn", "arg"]
        stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "body", "fn", "arg", "fn", "arg"]
        stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
}

#print axioms registration
end
end Reg.D5.S3.Geometry.Gluing.LiteralBarycentricSubdivisionStar.LiteralSecond
