import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.SufficiencyAux

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency

open _root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix Module

universe u v w z

abbrev natSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)
def natActual : Realization natSignature :=
  realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e)
def natRejected : Realization natSignature :=
  realize natSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem natDependence : ObservationalDependence natSignature natActual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  omega

private theorem zero_joint_control {a b : Type*} [Fintype b] :
    ∀ y₁ ∈ LinearMap.range (0 : Matrix a b ℂ).mulVecLin ⊔
      LinearMap.range (0 : Matrix a b ℂ).mulVecLin,
      ∀ y₂ ∈ LinearMap.range (0 : Matrix a b ℂ).mulVecLin ⊔
        LinearMap.range (0 : Matrix a b ℂ).mulVecLin,
        ∃ x, (0 : Matrix a b ℂ).mulVecLin x = y₁ ∧
          (0 : Matrix a b ℂ).mulVecLin x = y₂ := by
  intro y₁ hy₁ y₂ hy₂
  simp only [Matrix.mulVecLin_zero, LinearMap.range_zero, sup_idem,
    Submodule.mem_bot] at hy₁ hy₂
  subst y₁
  subst y₂
  refine ⟨0, ?_, ?_⟩ <;> simp

private theorem zero_vertical {a b : Type*} [Fintype b] :
    vRank (0 : Matrix a b ℂ) 0 = 2 * hRank (0 : Matrix a b ℂ) 0 := by
  simp [hRank, vRank, Matrix.fromCols_zero, Matrix.fromRows_zero]

private theorem zero_horizontal {a b : Type*} [Fintype b] :
    hRank (0 : Matrix a b ℂ) 0 = 2 * vRank (0 : Matrix a b ℂ) 0 := by
  simp [hRank, vRank, Matrix.fromCols_zero, Matrix.fromRows_zero]

namespace RankJoint

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {m : Type u} {n : Type v} {p : Type w} {q : Type z}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (hB : ∀ y₁ ∈ LinearMap.range B₁.mulVecLin ⊔ LinearMap.range B₂.mulVecLin,
      ∀ y₂ ∈ LinearMap.range B₁.mulVecLin ⊔ LinearMap.range B₂.mulVecLin,
      ∃ x, B₁.mulVecLin x = y₁ ∧ B₂.mulVecLin x = y₂),
    R.readout () () (tensorSum A₁ A₂ B₁ B₂).rank (finrank ℂ ↥(LinearMap.range A₁.mulVecLin ⊔ LinearMap.range A₂.mulVecLin) *
        finrank ℂ ↥(LinearMap.range B₁.mulVecLin ⊔ LinearMap.range B₂.mulVecLin))

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law natRejected := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit) (ULift.{z} Unit)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    0 0 0 0 zero_joint_control

def source_registration : Registration arena.{u,v,w,z} (type_of% @rank_tensorSum_of_jointSurjective) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@rank_tensorSum_of_jointSurjective, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@rank_tensorSum_of_jointSurjective) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.rank_tensorSum_of_jointSurjective.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency.RankJoint.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end RankJoint

namespace RankVertical

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {m : Type u} {n : Type v} {p : Type w} {q : Type z}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (hB : vRank B₁ B₂ = 2 * hRank B₁ B₂),
    R.readout () () (tensorSum A₁ A₂ B₁ B₂).rank (hRank A₁ A₂ * hRank B₁ B₂)

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law natRejected := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit) (ULift.{z} Unit)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    0 0 0 0 zero_vertical

def source_registration : Registration arena.{u,v,w,z} (type_of% @rank_tensorSum_of_vertical_saturated) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@rank_tensorSum_of_vertical_saturated, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@rank_tensorSum_of_vertical_saturated) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.rank_tensorSum_of_vertical_saturated.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency.RankVertical.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end RankVertical

namespace RankPTVertical

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {m : Type u} {n : Type v} {p : Type w} {q : Type z}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (hB : vRank B₁ B₂ = 2 * hRank B₁ B₂),
    R.readout () () (partialTranspose A₁ A₂ B₁ B₂).rank (vRank A₁ A₂ * hRank B₁ B₂)

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law natRejected := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit) (ULift.{z} Unit)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    0 0 0 0 zero_vertical

def source_registration : Registration arena.{u,v,w,z} (type_of% @rank_partialTranspose_of_vertical_saturated) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@rank_partialTranspose_of_vertical_saturated, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@rank_partialTranspose_of_vertical_saturated) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.rank_partialTranspose_of_vertical_saturated.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency.RankPTVertical.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end RankPTVertical

namespace Vertical

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {m : Type u} {n : Type v} {p : Type w} {q : Type z}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (hA : vRank A₁ A₂ = 2 * hRank A₁ A₂)
    (hB : vRank B₁ B₂ = 2 * hRank B₁ B₂),
    R.readout () () (partialTranspose A₁ A₂ B₁ B₂).rank (2 * (tensorSum A₁ A₂ B₁ B₂).rank)

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law natRejected := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit) (ULift.{z} Unit)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    0 0 0 0 zero_vertical zero_vertical

def source_registration : Registration arena.{u,v,w,z} (type_of% @saturation_of_vertical) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@saturation_of_vertical, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@saturation_of_vertical) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.saturation_of_vertical.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency.Vertical.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Vertical

namespace Horizontal

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {m : Type u} {n : Type v} {p : Type w} {q : Type z}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (hA : hRank A₁ A₂ = 2 * vRank A₁ A₂)
    (hB : hRank B₁ B₂ = 2 * vRank B₁ B₂),
    R.readout () () (partialTranspose A₁ A₂ B₁ B₂).rank (2 * (tensorSum A₁ A₂ B₁ B₂).rank)

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law natRejected := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit) (ULift.{z} Unit)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    0 0 0 0 zero_horizontal zero_horizontal

def source_registration : Registration arena.{u,v,w,z} (type_of% @saturation_of_horizontal) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@saturation_of_horizontal, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@saturation_of_horizontal) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.saturation_of_horizontal.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency.Horizontal.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Horizontal

namespace Sufficient

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {m : Type u} {n : Type v} {p : Type w} {q : Type z}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (h : (vRank A₁ A₂ = 2 * hRank A₁ A₂ ∧
        vRank B₁ B₂ = 2 * hRank B₁ B₂) ∨
      (hRank A₁ A₂ = 2 * vRank A₁ A₂ ∧
        hRank B₁ B₂ = 2 * vRank B₁ B₂)),
    R.readout () () (partialTranspose A₁ A₂ B₁ B₂).rank (2 * (tensorSum A₁ A₂ B₁ B₂).rank)

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law natRejected := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit) (ULift.{z} Unit)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    0 0 0 0 (Or.inl ⟨zero_vertical, zero_vertical⟩)

def source_registration : Registration arena.{u,v,w,z} (type_of% @sufficient) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@sufficient, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@sufficient) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.sufficient.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency.Sufficient.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Sufficient

end Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
