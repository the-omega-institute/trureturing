import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Observation.ThreeReadBudget
import Reg.Support.DependentFamily

/-! Source observations of the quadratic reading, with the complete original law. -/

namespace Reg.D5.S0.Observation.ThreeReadBudget

open _root_.D5.S0.Observation.ThreeReadBudget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- The original module, its algebraic dictionaries and its bilinear reading. -/
abbrev signature : Signature where
  Params := Σ V : Type u, Σ group : AddCommGroup V,
    Σ module : @Module ℝ V _ group.toAddCommMonoid,
      @BilinearReading V group module
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p f =>
    @threeReadQuadratic p.1 p.2.1 p.2.2.1 p.2.2.2 f)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/-- Only the quadratic observation is replaced; the full source law is retained. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} [group : AddCommGroup V] [module : Module ℝ V]
    (R : BilinearReading V) (U : V →ₗ[ℝ] V)
    (_hbudget : ThreeReadBudget R U),
    (∀ f, 0 ≤ r.readout () ⟨V, group, module, R⟩ f) ∧
      Set.range (threeReadSum U) ⊆ threeReadNullspace R

theorem actual_law : arena.{u}.Law actual := by
  exact @D5.S0.Observation.ThreeReadBudget.three_read_budget_nullspace.{u}

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hzero : ThreeReadBudget (0 : BilinearReading (ULift.{u} ℝ)) 0 := by
    intro f g n
    simp [threeReadQuadratic]
  have hb := (h (0 : BilinearReading (ULift.{u} ℝ)) 0 hzero).1 0
  norm_num [rejected, realize] at hb

/-- A genuine scalar bilinear observation, used only for audit dependence. -/
def sampleReading : BilinearReading (ULift.{u} ℝ) where
  toFun x := {
    toFun := fun y => x.down * y.down
    map_add' := by intro y z; simp [mul_add]
    map_smul' := by intro c y; simp [mul_left_comm] }
  map_add' := by intro x y; ext z; simp [add_mul]
  map_smul' := by intro c x; ext z; simp [mul_assoc]

def source_registration : Registration arena.{u}
    (type_of% @D5.S0.Observation.ThreeReadBudget.three_read_budget_nullspace.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℝ, inferInstance, inferInstance, sampleReading⟩,
      ULift.up 0, ULift.up 1, ?_⟩
    norm_num [actual, realize, threeReadQuadratic, sampleReading]

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@D5.S0.Observation.ThreeReadBudget.three_read_budget_nullspace.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S0.Observation.ThreeReadBudget.unit
  realizationName := `Reg.D5.S0.Observation.ThreeReadBudget.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p f =>
    @threeReadQuadratic p.1 p.2.1 p.2.2.1 p.2.2.2 f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Observation.ThreeReadBudget
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S0.Observation.ThreeReadBudget
