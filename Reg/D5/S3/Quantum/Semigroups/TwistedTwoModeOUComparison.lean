import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison

/-! Complete pure-state attenuation telescope with the actual real comparison readout. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open _root_.D5.S3.Quantum.Foundation.TwoKrausRankOneAttenuation
open _root_.D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison

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

abbrev arena : Arena where
  signature := signature
  Law O := ∀ (q : ℝ) (_hq0 : 0 ≤ q) (_hq1 : q ≤ 1)
    (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) (_hψ : ‖ψ‖ = 1),
    let u := WithLp.ofLp ψ
    O.readout () () ‖toEuclideanCLM (n := Fin 2 × Fin 2) (𝕜 := ℂ)
      (jumpMap (modeJump 0) q (jumpMap (modeJump 1) q (vecMulVec u (star u))))‖
      (1 - q * (1-q) * directionalBudget ψ / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 le_rfl zero_le_one (EuclideanSpace.single (0,0) 1)
    (by simp [EuclideanSpace.single])

def family : Registration arena (type_of% two_mode_pure_state_attenuation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨two_mode_pure_state_attenuation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he : (1 : ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
    norm_num at he

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    two_mode_pure_state_attenuation (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison.unit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison
