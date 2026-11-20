import D5.S3.StatisticalMechanics.HardCore.HardSquareStraightBlockObstruction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source equivalence for the selected blocked-weight operand. -/

namespace Reg.D5.S3.StatisticalMechanics.HardCore.HardSquareStraightBlockObstruction

open _root_.D5.S3.StatisticalMechanics.HardCore.HardSquareStraightBlockObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

/-- At each width, observe how the first corner fugacity changes the weight
as a function of the other three fugacities and the whole face. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℂˣ)
    (fun k => ℂˣ → ℂˣ → ℂˣ → Weight k)

def actual : Realization signature :=
  realize signature (fun _ k A => @blocked k A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law T :=
    ∀ (k : ℕ) (_hk : 3 ≤ k) (A B C D : ℂˣ) (Ω : Set ℂ)
      (_hΩopen : IsOpen Ω) (_hΩconn : IsConnected Ω),
      ¬ HasFamily k Ω (T.readout () k A B C D)

/-- The all-zero family satisfies the face equation and realizes the zero target. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h 3 (by decide) 1 1 1 1 Set.univ isOpen_univ isConnected_univ
  refine ⟨fun _ _ _ _ _ _ => 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv a b c d hface
    rfl
  · intros
    exact differentiableOn_const (0 : ℂ)
  · intros
    exact differentiableOn_const (0 : ℂ)
  · intro p hp q hq r hr
    refine ⟨1, fun a b c d e f => ?_⟩
    simp [EqAt]
  · exact ⟨0, Set.mem_univ _, 0, Set.mem_univ _, rfl⟩

private def vacant : Word 3 := ⟨fun _ => false, by simp⟩

private def firstOccupied : Word 3 :=
  ⟨fun i => decide (i.val = 0), by
    intro i j hj
    simp only [decide_eq_true_eq]
    omega⟩

private theorem firstFace : FaceSupport firstOccupied vacant vacant vacant := by
  simp [FaceSupport, H, V, vacant]

private theorem occupation_first : occ firstOccupied = 1 := by
  decide

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let negOne : ℂˣ := Units.mk0 (-1) (by norm_num)
  refine ⟨3, 1, negOne, ?_⟩
  intro he
  have h := congrFun (congrFun (congrFun he (1 : ℂˣ)) (1 : ℂˣ)) (1 : ℂˣ)
  have hf := congrFun (congrFun (congrFun (congrFun h firstOccupied) vacant) vacant) vacant
  change blocked (1 : ℂˣ) 1 1 1 firstOccupied vacant vacant vacant =
    blocked negOne 1 1 1 firstOccupied vacant vacant vacant at hf
  norm_num [blocked, firstFace, occupation_first, negOne] at hf

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.HardCore.HardSquareStraightBlockObstruction.auditUnit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.HardCore.HardSquareStraightBlockObstruction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k A => @blocked k A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.HardCore.HardSquareStraightBlockObstruction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "fn", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.StatisticalMechanics.HardCore.HardSquareStraightBlockObstruction
