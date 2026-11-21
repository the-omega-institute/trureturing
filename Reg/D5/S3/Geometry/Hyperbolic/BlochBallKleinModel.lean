import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Hyperbolic.BlochBallKleinModel
import Reg.Support.DependentFamily

/-! Source-bound audit of the Klein model on the open Bloch ball. The readout is the norm of the
filtered Bloch vector `blochFilter g r` in the bound `‖blochFilter g r‖ ≤ 1` of the clause that the
filter of an invertible matrix keeps the closed ball. -/

namespace Reg.D5.S3.Geometry.Hyperbolic.BlochBallKleinModel

open _root_.D5.S3.Geometry.Hyperbolic.BlochBallKleinModel
open _root_.D5.S3.Geometry.HyperbolicUpperHalfSpace (HyperbolicThreeSpace)
open _root_.D5.S3.Quantum.Information.ActualPureQubitCostInfimum (blochMatrix)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped InnerProductSpace Matrix ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Bloch vectors observed through their Euclidean norm. -/
abbrev signature : Signature where
  Params := Unit
  State _ := EuclideanSpace ℝ (Fin 3)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ v => ‖v‖) (fun e => nomatch e)

/-- The constant reading `2`. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- Retain the complete five-clause statement of `bloch_ball_hyperbolic`; only the norm of the
filtered vector in the bound `‖blochFilter g r‖ ≤ 1` of the fourth clause is read out. -/
abbrev arena : Arena where
  signature := signature
  Law ρ :=
    (∃ Φ : {r : EuclideanSpace ℝ (Fin 3) // ‖r‖ < 1} ≃ HyperbolicThreeSpace,
      ∀ r s, Real.cosh (dist (Φ r) (Φ s)) = kleinCosh r s) ∧
    (∀ r : EuclideanSpace ℝ (Fin 3), blochFilter 1 r = r) ∧
    (∀ (g h : Matrix (Fin 2) (Fin 2) ℂ) (r : EuclideanSpace ℝ (Fin 3)),
      (Matrix.trace (g * blochMatrix 1 r * gᴴ)).re ≠ 0 →
        blochFilter h (blochFilter g r) = blochFilter (h * g) r) ∧
    (∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.det ≠ 0 →
      (∀ r : EuclideanSpace ℝ (Fin 3), ‖r‖ ≤ 1 →
        ρ.readout () () (blochFilter g r) ≤ 1 ∧ (‖blochFilter g r‖ < 1 ↔ ‖r‖ < 1)) ∧
      ∀ r s : EuclideanSpace ℝ (Fin 3), ‖r‖ < 1 → ‖s‖ < 1 →
        kleinCosh (blochFilter g r) (blochFilter g s) = kleinCosh r s) ∧
    ∀ r : EuclideanSpace ℝ (Fin 3), ‖r‖ < 1 →
      ∃ g : Matrix (Fin 2) (Fin 2) ℂ, g.PosDef ∧ g.det = 1 ∧ blochFilter g 0 = r

/-- For the identity matrix and the centre the rejected reading would give `2 ≤ 1`. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := ((h.2.2.2.1 1 (by simp)).1 0 (by simp)).1
  change (2 : ℝ) ≤ 1 at hh
  norm_num at hh

/-- The centre has norm `0` and the first basis vector has norm `1`. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, EuclideanSpace.single 0 1, ?_⟩
  change ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ≠ ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖
  rw [norm_zero]
  refine (norm_pos_iff.2 fun h => ?_).ne
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
  simp at h0

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @bloch_ball_hyperbolic

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bloch_ball_hyperbolic, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def bloch_ball_hyperbolic_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bloch_ball_hyperbolic) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Geometry.Hyperbolic.BlochBallKleinModel.bloch_ball_hyperbolic_unit
  realizationName := `Reg.D5.S3.Geometry.Hyperbolic.BlochBallKleinModel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => ‖v‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Hyperbolic.BlochBallKleinModel
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg", "body", "body", "fn",
        "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Geometry.Hyperbolic.BlochBallKleinModel
