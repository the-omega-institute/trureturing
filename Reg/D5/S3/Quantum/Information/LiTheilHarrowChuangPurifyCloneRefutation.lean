import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the rank equality for a normalized pure vector. -/

namespace Reg.D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.VecPureRankOne
open _root_.D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation (vecPure_rank_one)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Observe equality between the computed matrix rank and its asserted value. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} [Fintype a] [DecidableEq a]
    (v : a → ℂ) (_htr : (Matrix.vecMulVec v (star v)).trace = 1),
    R.readout () () (Matrix.vecMulVec v (star v)).rank 1

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (fun _ : ULift.{u} Unit => (1 : ℂ)) (by simp [Matrix.trace, Matrix.vecMulVec_apply])

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact Nat.one_ne_zero (Eq.mp (congrFun h 0) rfl)

def source_registration : Registration arena.{u} (type_of% @vecPure_rank_one.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@vecPure_rank_one, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@vecPure_rank_one.{u}) (Realization signature) Unit Unit := {
  unitName := .str ``vecPure_rank_one "__information_unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.vecPure_rank_one
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.VecPureRankOne
