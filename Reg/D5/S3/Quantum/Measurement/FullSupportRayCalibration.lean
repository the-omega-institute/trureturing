import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.FullSupportRayCalibration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Field.Rat

/-! The comparison scalar must remain observable on a supported coordinate. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.FullSupportRayCalibration
open LeanInformationAudit

namespace Reg.D5.S3.Quantum.Measurement.FullSupportRayCalibration
noncomputable section
universe u v w z

abbrev signature : Signature where
  Params := Type u
  State K := K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ K := K
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)
def discarded : Realization signature :=
  realize signature (fun _ _ x => Classical.choice ⟨x⟩) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {K : Type u} {V : Type v} {W : Type w} {ι : Type z}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Fintype ι]
    (b : Module.Basis ι K V) (J T : V →ₗ[K] W) (hJ : Function.Injective J) (a : ι → K)
    (hb : ∀ i, T (b i) = a i • J (b i)) (u : V) (c : K),
    (T u = c • J u ↔ ∀ i, b.repr u i ≠ 0 → a i = R.readout () K c) ∧
    ((∀ i, b.repr u i ≠ 0) → (T u = c • J u ↔ T = c • J))

private def liftEquiv : ULift.{v} ℚ ≃ₗ[ULift.{u} ℚ] ULift.{w} ℚ where
  toFun x := ⟨x.down⟩
  invFun x := ⟨x.down⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem discarded_fails : ¬arena.{u,v,w,z}.Law discarded := by
  intro law
  let K := ULift.{u} ℚ
  let I := ULift.{z} Unit
  let b := (Module.Basis.singleton I K).map (liftEquiv.{u,u,v})
  let J := liftEquiv.{u,v,w}
  let i : I := ⟨()⟩
  have collapse (c : K) : c = Classical.choice (⟨c⟩ : Nonempty K) := by
    have h := (law b J.toLinearMap (c • J.toLinearMap) J.injective
      (fun _ => c) (fun _ => rfl) (b i) c).1.mp rfl
    exact h i (by simp)
  exact (zero_ne_one : (0 : K) ≠ 1) ((collapse 0).trans (collapse 1).symm)

def family : Registration arena.{u,v,w,z} (type_of% @support_calibration.{u,v,w,z}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨support_calibration, discarded, discarded_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨discarded, ?_, rfl, discarded_fails⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    exact ⟨ULift.{u} ℚ, (0 : ULift.{u} ℚ), (1 : ULift.{u} ℚ), (zero_ne_one : (0 : ULift.{u} ℚ) ≠ 1)⟩

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Measurement.FullSupportRayCalibration.support_calibration.{u,v,w,z})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Measurement.FullSupportRayCalibration.unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.FullSupportRayCalibration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨family.{u,v,w,z}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.FullSupportRayCalibration
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "body", "arg"]
      stateBinder := 17
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Measurement.FullSupportRayCalibration
