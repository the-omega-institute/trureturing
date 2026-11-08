import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.FlatPairJointBlocks
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.FlatPairJointBlocks
open scoped InnerProductSpace
open Module.End
open Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace Reg.D5.S3.Quantum.Algebra.FlatPairJointBlocks
universe u

/-- The original carrier, both metric instances, finite-dimensional evidence and D
are parameters; A varies over all original endomorphisms. -/
def signature : Signature where
  Params := Σ (F : Type u) (n : NormedAddCommGroup F),
    letI := n
    Σ ip : InnerProductSpace ℝ F,
      letI := ip
      {D : F →ₗ[ℝ] F // FiniteDimensional ℝ F}
  State p :=
    letI := p.2.1
    letI := p.2.2.1
    p.1 →ₗ[ℝ] p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

/-- A whole-source family, with actual truth readout and counterfactual interventions. -/
def family : Registration
    {
    signature := signature.{u}
    Law R := ∀ {F : Type u} [n : NormedAddCommGroup F] [ip : InnerProductSpace ℝ F]
      [fd : FiniteDimensional ℝ F] (K D : F →ₗ[ℝ] F),
      R.readout () ⟨F,n,ip,D,fd⟩ K=true ↔
        (∀ x y,⟪K x,y⟫_ℝ = -⟪x,K y⟫_ℝ) ∧
        (∀ x y,⟪D x,y⟫_ℝ = -⟪x,D y⟫_ℝ) ∧ -(K*K)-D*D=1 }
    (type_of% (@flat_pair_joint_blocks_iff.{u})) := by
  let actual : Realization signature.{u} := realize signature (fun _ p K =>
    letI := p.2.1
    letI := p.2.2.1
    letI := p.2.2.2.property
    decide (HasFlatPairJointBlocks K p.2.2.2.val)) (fun e => nomatch e)
  let bad : Realization signature.{u} := realize signature
    (fun _ _ _ => false) (fun e => nomatch e)
  let arena : Arena := {
    signature := signature.{u}
    Law R := ∀ {F : Type u} [n : NormedAddCommGroup F] [ip : InnerProductSpace ℝ F]
      [fd : FiniteDimensional ℝ F] (K D : F →ₗ[ℝ] F),
      R.readout () ⟨F,n,ip,D,fd⟩ K=true ↔
        (∀ x y,⟪K x,y⟫_ℝ = -⟪x,K y⟫_ℝ) ∧
        (∀ x y,⟪D x,y⟫_ℝ = -⟪x,D y⟫_ℝ) ∧ -(K*K)-D*D=1 }
  have bridge : (type_of% (@flat_pair_joint_blocks_iff.{u})) ↔ arena.Law actual := by
    simp only [arena,actual,realize,decide_eq_true_eq]
  have positive : arena.Law actual := bridge.mp (@flat_pair_joint_blocks_iff.{u})
  have rejected : ¬ arena.Law bad := by
    intro h
    let Z := EuclideanSpace ℝ (ULift.{u} (Fin 0))
    have hz : (-(0*0)-(0:Z →ₗ[ℝ] Z)*0)=(1:Z →ₗ[ℝ] Z) := Subsingleton.elim _ _
    have ht := @h Z inferInstance inferInstance inferInstance 0 0
    exact Bool.false_ne_true (ht.mpr ⟨by simp,by simp,hz⟩)
  change Registration arena (type_of% (@flat_pair_joint_blocks_iff.{u}))
  refine {
    actual := actual
    bridge := bridge
    variation := ⟨positive,bad,rejected⟩
    sensitivity := ?_
    dependence := ?_ }
  · constructor
    · intro i
      refine ⟨bad,?_,rfl,rejected⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  · intro i
    let H := EuclideanSpace ℝ (ULift.{u} (Fin 2))
    let q : H := EuclideanSpace.single (ULift.up 0) 1
    let r : H := EuclideanSpace.single (ULift.up 1) 1
    let J : H →ₗ[ℝ] H := (innerSL ℝ q).toLinearMap.smulRight r -
      (innerSL ℝ r).toLinearMap.smulRight q
    have hJ : ∀ x y,⟪J x,y⟫_ℝ = -⟪x,J y⟫_ℝ := by
      intro x y
      simp only [J,LinearMap.sub_apply,LinearMap.smulRight_apply,
        ContinuousLinearMap.coe_coe,innerSL_apply_apply,inner_sub_left,inner_sub_right,
        real_inner_smul_left,real_inner_smul_right]
      rw [real_inner_comm x r,real_inner_comm x q]
      ring
    have hflat : -(J*J)-(0:H →ₗ[ℝ] H)*0=1 := by
      ext x j
      rcases j with ⟨j⟩
      fin_cases j <;>
        simp [J,q,r,EuclideanSpace.inner_single_left,PiLp.single_apply,
          LinearMap.smulRight_apply,Module.End.mul_apply]
    have hj : HasFlatPairJointBlocks J (0:H →ₗ[ℝ] H) :=
      (flat_pair_joint_blocks_iff _ _).2 ⟨hJ,by simp,hflat⟩
    have hzero : ¬ HasFlatPairJointBlocks (0:H →ₗ[ℝ] H) 0 := by
      intro h
      have hh := (flat_pair_joint_blocks_iff _ _).1 h |>.2.2
      have hc := congrArg (fun T : H →ₗ[ℝ] H => T q (ULift.up 0)) hh
      norm_num [q,PiLp.single_apply] at hc
    refine ⟨⟨H,inferInstance,inferInstance,0,inferInstance⟩,J,0,?_⟩
    change decide (HasFlatPairJointBlocks J (0:H →ₗ[ℝ] H)) ≠
      decide (HasFlatPairJointBlocks (0:H →ₗ[ℝ] H) 0)
    rw [decide_eq_true hj,decide_eq_false hzero]
    decide

/-- The selected readout is the original complete-frame predicate, not a finite catalog. -/
def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@flat_pair_joint_blocks_iff.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.FlatPairJointBlocks.flat_pair_joint_blocks_iff.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.FlatPairJointBlocks.family
  realizationSource := none
  generated := false
  arena := .source ⟨{
    signature := signature.{u}
    Law R := ∀ {F : Type u} [n : NormedAddCommGroup F] [ip : InnerProductSpace ℝ F]
      [fd : FiniteDimensional ℝ F] (K D : F →ₗ[ℝ] F),
      R.readout () ⟨F,n,ip,D,fd⟩ K=true ↔
        (∀ x y,⟪K x,y⟫_ℝ = -⟪x,K y⟫_ℝ) ∧
        (∀ x y,⟪D x,y⟫_ℝ = -⟪x,D y⟫_ℝ) ∧ -(K*K)-D*D=1 }⟩
  objectArena := .source ⟨{
    signature := signature.{u}
    Law R := ∀ {F : Type u} [n : NormedAddCommGroup F] [ip : InnerProductSpace ℝ F]
      [fd : FiniteDimensional ℝ F] (K D : F →ₗ[ℝ] F),
      R.readout () ⟨F,n,ip,D,fd⟩ K=true ↔
        (∀ x y,⟪K x,y⟫_ℝ = -⟪x,K y⟫_ℝ) ∧
        (∀ x y,⟪D x,y⟫_ℝ = -⟪x,D y⟫_ℝ) ∧ -(K*K)-D*D=1 }⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source ({
    signature := signature.{u}
    Law R := ∀ {F : Type u} [n : NormedAddCommGroup F] [ip : InnerProductSpace ℝ F]
      [fd : FiniteDimensional ℝ F] (K D : F →ₗ[ℝ] F),
      R.readout () ⟨F,n,ip,D,fd⟩ K=true ↔
        (∀ x y,⟪K x,y⟫_ℝ = -⟪x,K y⟫_ℝ) ∧
        (∀ x y,⟪D x,y⟫_ℝ = -⟪x,D y⟫_ℝ) ∧ -(K*K)-D*D=1 }) ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p K =>
    letI := p.2.1
    letI := p.2.2.1
    letI := p.2.2.2.property
    decide (HasFlatPairJointBlocks K p.2.2.2.val)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.FlatPairJointBlocks
    definition := none
    coordinates := #[0,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Algebra.FlatPairJointBlocks
