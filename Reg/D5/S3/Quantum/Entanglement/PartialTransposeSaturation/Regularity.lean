import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regularity
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regularity

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regularity
open _root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting
open _root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.ChainSplitting.FinitePair
open Module LinearMap
open scoped TensorProduct

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev emptyPencil : Pencil ℂ where
  domain := Fin 0 → ℂ
  codomain := Fin 0 → ℂ
  first := 0
  second := 0

private theorem emptyReduced : RightReduced emptyPencil := by
  intro r u hu
  change (u (Fin.last r) : Fin 0 → ℂ) = 0
  funext i
  exact Fin.elim0 i

private abbrev identityPencil : Pencil ℂ where
  domain := ℂ
  codomain := ℂ
  first := LinearMap.id
  second := 0

private theorem identityReduced : RightReduced identityPencil := by
  intro r u hu
  have hc : (@Fin.cons (r + 1) (fun _ => ℂ)) 0 (fun _ => 0) = 0 := by
    funext i
    cases i using Fin.cases <;> rfl
  change Fin.snoc (α := fun _ => ℂ) u 0 -
    (@Fin.cons (r + 1) (fun _ => ℂ)) 0 (fun _ => 0) = 0 at hu
  rw [hc, sub_zero] at hu
  have h := congrFun hu (Fin.last r).castSucc
  rw [Fin.snoc_castSucc] at h
  exact h

private abbrev independentPencil : Pencil ℂ where
  domain := Fin 2 → ℂ
  codomain := ℂ
  first := LinearMap.proj 0
  second := LinearMap.proj 1

private theorem independentPair : LinearIndependent ℂ
    ![independentPencil.first, independentPencil.second] := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have he := congrArg (fun f : (Fin 2 → ℂ) →ₗ[ℂ] ℂ => f ![0, 1]) h
    change (1 : ℂ) = 0 at he
    exact one_ne_zero he
  · intro a h
    have he := congrArg (fun f : (Fin 2 → ℂ) →ₗ[ℂ] ℂ => f ![1, 0]) h
    change a * 0 = 1 at he
    simpa only [mul_zero, zero_ne_one] using he

namespace DualRank

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  omega

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p q : Pencil ℂ), RightReduced p →
    Module.finrank ℂ p.domain = Module.finrank ℂ p.codomain →
    R.readout () ()
      (Module.finrank ℂ (LinearMap.range
        (TensorProduct.map p.first.dualMap q.first +
          TensorProduct.map p.second.dualMap q.second)))
      (Module.finrank ℂ (LinearMap.range
        (TensorProduct.map p.first q.first + TensorProduct.map p.second q.second)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h emptyPencil emptyPencil emptyReduced rfl

def source_registration : Registration arena (type_of% @tensor_rank_dual_eq_of_reduced) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tensor_rank_dual_eq_of_reduced, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@tensor_rank_dual_eq_of_reduced) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regularity.tensor_rank_dual_eq_of_reduced.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regularity.DualRank.source_registration
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
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regularity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end DualRank

namespace PositiveRank

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℕ) < 1 := Eq.mp (congrFun he 1) (by decide : (0 : ℕ) < 1)
  omega

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p q : Pencil ℂ), RightReduced p →
    Module.finrank ℂ p.domain = Module.finrank ℂ p.codomain →
    0 < Module.finrank ℂ p.domain → LinearIndependent ℂ ![q.first, q.second] →
    R.readout () () 0
      (Module.finrank ℂ (LinearMap.range
        (TensorProduct.map p.first q.first + TensorProduct.map p.second q.second)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h identityPencil independentPencil identityReduced rfl
    (by change 0 < finrank ℂ ℂ; rw [Module.finrank_self]; decide) independentPair

def source_registration : Registration arena (type_of% @tensor_rank_pos_of_reduced) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tensor_rank_pos_of_reduced, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@tensor_rank_pos_of_reduced) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regularity.tensor_rank_pos_of_reduced.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regularity.PositiveRank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regularity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end PositiveRank

end Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Regularity
