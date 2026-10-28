import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.ProjectionRange.SimplexFrames
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open CategoryTheory Convexity ProjectionRange
open scoped Simplicial Matrix ComplexOrder Matrix.Norms.Elementwise

namespace Reg.D5.S3.Geometry.ProjectionRange.SimplexFrames
noncomputable section
universe u v

abbrev signature : Signature where
  Params := Σ n : ℕ, Σ r : ℕ, ℕ
  State p := Fin p.2.1 → C((SimplexCategory.toTop.{v}.obj ⦋p.2.2⦌), V p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.2.1 → C((SimplexCategory.toTop.{v}.obj ⦋p.2.2⦌), V p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def absentAnchor : ∀ (_ : signature.{v}.Anchor) p, signature.{v}.State p :=
  fun e => nomatch e

def actual : Realization signature.{v} :=
  realize signature.{v} (fun _ _ s => s) absentAnchor

def rejected : Realization signature.{v} :=
  realize signature.{v} (fun _ _ _ => 0) absentAnchor

abbrev arena : Arena where
  signature := signature.{v}
  Law ρ := ∀ {B : Type u} [TopologicalSpace B] {n r k : ℕ}
    (P : B → Matrix (Fin n) (Fin n) ℂ)
    (_hP : Continuous P) (_hstar : ∀ x, (P x)ᴴ = P x)
    (_hidem : ∀ x, P x * P x = P x)
    (_hrank : ∀ x, (P x).rank = r) (_hk : k ≤ 3)
    (σ : C((SimplexCategory.toTop.{v}.obj ⦋k⦌), B)),
    ∃ (s : Fin r → C((SimplexCategory.toTop.{v}.obj ⦋k⦌), V n))
      (a : C((SimplexCategory.toTop.{v}.obj ⦋k⦌), V n →L[ℂ] V r)),
      (∀ x i, s i x ∈ rangeSubmodule P (σ x)) ∧
      (∀ x i, a x ((ρ.readout () ⟨n, r, k⟩ s) i x) =
        EuclideanSpace.single i (1 : ℂ)) ∧
      (∀ x (v : Fiber P (σ x)),
        ∑ i, ((a x (v : V n)) i) • s i x = (v : V n))

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  classical
  intro h
  let B := ULift.{u} Unit
  let X := SimplexCategory.toTop.{v}.obj ⦋0⦌
  let σ : C(X, B) := ContinuousMap.const X ⟨()⟩
  obtain ⟨s, a, _, hc, _⟩ := @h B inferInstance 1 1 0 (fun _ => 1)
    continuous_const (by intro x; simp) (by intro x; simp)
    (by intro x; simp) (by omega) σ
  let x : X := ULift.up (StdSimplex.single (0 : Fin 1))
  have he := hc x (0 : Fin 1)
  change a x 0 = EuclideanSpace.single (0 : Fin 1) (1 : ℂ) at he
  rw [map_zero] at he
  have hv := congrArg (fun z : V 1 => z (0 : Fin 1)) he
  norm_num [EuclideanSpace.single, PiLp.single_apply] at hv

def family : Registration arena.{u,v}
    (type_of% (@range_projection_simplex_frames.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@range_projection_simplex_frames.{u,v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    classical
    intro i
    let X := SimplexCategory.toTop.{v}.obj ⦋0⦌
    let e : V 1 := EuclideanSpace.single (0 : Fin 1) (1 : ℂ)
    let x : X := ULift.up (StdSimplex.single (0 : Fin 1))
    refine ⟨⟨1, 1, 0⟩, 0, (fun _ => ContinuousMap.const X e), ?_⟩
    intro he
    change (0 : Fin 1 → C(X, V 1)) = (fun _ => ContinuousMap.const X e) at he
    have hv := congrArg (fun s => (s (0 : Fin 1) x) (0 : Fin 1)) he
    norm_num [e, EuclideanSpace.single, PiLp.single_apply] at hv

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@range_projection_simplex_frames.{u,v})
      (Realization signature.{v}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.ProjectionRange.SimplexFrames.columns
  realizationName := `Reg.D5.S3.Geometry.ProjectionRange.SimplexFrames.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{v} (fun _ _ s => s) absentAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Geometry.ProjectionRange.SimplexFrames, definition := none, coordinates := #[2, 3, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn"], stateBinder := 12, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration_1

end

end Reg.D5.S3.Geometry.ProjectionRange.SimplexFrames
