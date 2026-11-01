import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.DatkoStability
import Reg.Support.DependentFamily

/-! Source-bound comparison readout for the full real Banach Datko equivalence. -/

open MeasureTheory Set
open scoped NNReal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.DatkoStability
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.DatkoStability

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

/-- The observed real comparison is inside the all-time operator estimate.
The original universe, complete real normed space, semigroup, individual-vector
energy condition and both directions remain in the law. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    [CompleteSpace E],
    (∀ x : E, IntegrableOn (fun t : ℝ => ‖S (Real.toNNReal t) x‖ ^ 2)
      (Ioi 0) volume) ↔
    ∃ M ω : ℝ, 1 ≤ M ∧ 0 < ω ∧
      ∀ t : ℝ≥0, R.readout () () ‖S t‖ (M * Real.exp (-ω * (t : ℝ)))

private theorem actual_law : arena.{u}.Law actual :=
  @integrable_sq_orbit_iff_exponential_stability.{u}

private def zeroSpaceSemigroup :
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup PUnit.{u+1} where
  operator _ := ContinuousLinearMap.id ℝ _
  operator_zero := rfl
  operator_add _ _ := by ext x
  opNorm_le_one _ := ContinuousLinearMap.norm_id_le
  continuous_orbit x := continuous_const

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hi : ∀ x : PUnit.{u+1}, IntegrableOn
      (fun t : ℝ => ‖zeroSpaceSemigroup (Real.toNNReal t) x‖ ^ 2) (Ioi 0) volume := by
    intro x
    simp
  obtain ⟨M, ω, hM, hω, hb⟩ := (h zeroSpaceSemigroup).mp hi
  exact hb 0

def family : Registration arena.{u}
    (type_of% (@integrable_sq_orbit_iff_exponential_stability.{u})) where
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
    (@integrable_sq_orbit_iff_exponential_stability.{u})
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.DatkoStability.datkoUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.DatkoStability.family
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
    owner := `D5.S3.Quantum.Analysis.DatkoStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "body",
        "arg", "body", "arg", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Quantum.Analysis.DatkoStability
