import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
import Reg.Support.SingleDependentReadout
import Mathlib.Algebra.Ring.ULift

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.SufficiencyAux

open _root_.D5.S3.Quantum.Entanglement.PartialTransposeSaturation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Module LinearMap Matrix
open scoped TensorProduct

universe u v w z a b c d t

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

abbrev propSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Prop) (fun _ => Prop → Prop)
def propActual : Realization propSignature :=
  realize propSignature (fun _ _ x y => x ↔ y) (fun e => nomatch e)
def propRejected : Realization propSignature :=
  realize propSignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem propDependence : ObservationalDependence propSignature propActual := by
  intro role
  refine ⟨(), True, False, ?_⟩
  intro he
  have h : False ↔ True := Eq.mp (congrFun he True) Iff.rfl
  exact h.mpr trivial

abbrev matrixSignature : Signature where
  Params := Σ _ : Type u, Σ _ : Type v, Σ _ : Type w, Type z
  State p := Matrix (p.1 × p.2.2.1) (p.2.1 × p.2.2.2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (p.1 × p.2.2.1) (p.2.1 × p.2.2.2) ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def matrixActual : Realization matrixSignature.{u,v,w,z} :=
  realize matrixSignature (fun _ _ x y => x = y) (fun e => nomatch e)
def matrixRejected : Realization matrixSignature.{u,v,w,z} :=
  realize matrixSignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem matrixDependence : ObservationalDependence matrixSignature.{u,v,w,z} matrixActual := by
  intro role
  refine ⟨⟨ULift.{u} Unit, ULift.{v} Unit, ULift.{w} Unit, ULift.{z} Unit⟩,
    0, (fun _ _ => 1), ?_⟩
  intro he
  have h := Eq.mp (congrFun he 0) rfl
  have hh := congrArg (fun M : Matrix
      (ULift.{u} Unit × ULift.{w} Unit) (ULift.{v} Unit × ULift.{z} Unit) ℂ =>
    M (⟨()⟩, ⟨()⟩) (⟨()⟩, ⟨()⟩)) h
  change (1 : ℂ) = 0 at hh
  exact one_ne_zero hh

namespace ZeroDetection

abbrev arena : Arena where
  signature := matrixSignature.{u,v,w,z}
  Law R := ∀ {m : Type u} {n : Type v} {p : Type w} {q : Type z}
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (hA : LinearIndependent ℂ ![A₁, A₂]),
    R.readout () ⟨m, n, p, q⟩ (tensorSum A₁ A₂ B₁ B₂) 0 ↔
      B₁ = 0 ∧ B₂ = 0

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law matrixRejected := by
  intro h
  let A₁ : Matrix PUnit.{u+1} (ULift.{v} (Fin 2)) ℂ :=
    fun _ j => if j.down = 0 then 1 else 0
  let A₂ : Matrix PUnit.{u+1} (ULift.{v} (Fin 2)) ℂ :=
    fun _ j => if j.down = 1 then 1 else 0
  have hA : LinearIndependent ℂ ![A₁, A₂] := by
    rw [linearIndependent_fin2]
    constructor
    · intro he
      have hh := congrArg (fun M : Matrix PUnit.{u+1} (ULift.{v} (Fin 2)) ℂ =>
        M PUnit.unit ⟨1⟩) he
      change (1 : ℂ) = 0 at hh
      exact one_ne_zero hh
    · intro x he
      have hh := congrArg (fun M : Matrix PUnit.{u+1} (ULift.{v} (Fin 2)) ℂ =>
        M PUnit.unit ⟨0⟩) he
      change x * 0 = 1 at hh
      simpa only [mul_zero, zero_ne_one] using hh
  have he := @h PUnit.{u+1} (ULift.{v} (Fin 2)) PUnit.{w+1} PUnit.{z+1}
    A₁ A₂ 0 0 hA
  exact he.mpr ⟨rfl, rfl⟩

def source_registration : Registration arena.{u,v,w,z} (type_of% @tensorSum_eq_zero_iff) where
  actual := matrixActual
  bridge := Iff.rfl
  variation := ⟨@tensorSum_eq_zero_iff, matrixRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨matrixRejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := matrixDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@tensorSum_eq_zero_iff) (Realization matrixSignature.{u,v,w,z}) Type Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.tensorSum_eq_zero_iff.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.SufficiencyAux.ZeroDetection.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature.{u,v,w,z} matrixActual.readout matrixActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #[ "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn" ]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ZeroDetection

namespace RankChange

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {m : Type u} {n : Type v} {p : Type w} {q : Type z}
    [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    (A₁ A₂ : Matrix m n ℂ) (B₁ B₂ : Matrix p q ℂ)
    (P : Matrix m m ℂ) (Q : Matrix n n ℂ)
    (R' : Matrix p p ℂ) (S : Matrix q q ℂ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (hR : IsUnit R'.det) (hS : IsUnit S.det),
    R.readout () ()
      (tensorSum (P * A₁ * Q) (P * A₂ * Q) (R' * B₁ * S) (R' * B₂ * S)).rank
      (tensorSum A₁ A₂ B₁ B₂).rank

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law natRejected := by
  intro h
  exact @h (ULift.{u} Unit) (ULift.{v} Unit) (ULift.{w} Unit) (ULift.{z} Unit)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    0 0 0 0 1 1 1 1 (by simp) (by simp) (by simp) (by simp)

def source_registration : Registration arena.{u,v,w,z} (type_of% @rank_tensorSum_change) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@rank_tensorSum_change, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@rank_tensorSum_change) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.rank_tensorSum_change.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.SufficiencyAux.RankChange.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature natActual.readout natActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[ "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn" ]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end RankChange

namespace JointControl

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A₁ A₂ : Matrix m n ℂ),
    R.readout () () (vRank A₁ A₂) (2 * hRank A₁ A₂) ↔
      (∀ y₁ ∈ LinearMap.range A₁.mulVecLin ⊔ LinearMap.range A₂.mulVecLin,
        ∀ y₂ ∈ LinearMap.range A₁.mulVecLin ⊔ LinearMap.range A₂.mulVecLin,
          ∃ x, A₁.mulVecLin x = y₁ ∧ A₂.mulVecLin x = y₂)

private theorem rejected_law : ¬ arena.{u,v}.Law natRejected := by
  intro h
  have he := @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance 0 0
  exact he.mpr (by
    intro y₁ hy₁ y₂ hy₂
    have h₁ : y₁ = 0 := by simpa using hy₁
    have h₂ : y₂ = 0 := by simpa using hy₂
    exact ⟨0, by simpa using h₁.symm, by simpa using h₂.symm⟩)

def source_registration : Registration arena.{u,v} (type_of% @joint_control_iff) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@joint_control_iff, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@joint_control_iff) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.joint_control_iff.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.SufficiencyAux.JointControl.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature natActual.readout natActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[ "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn" ]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end JointControl

namespace CoordinateRank

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {U : Type u} {V : Type v} {U' : Type w} {V' : Type z}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup U'] [Module ℂ U'] [AddCommGroup V'] [Module ℂ V']
    {a : Type a} {b : Type b} {c : Type c} {d : Type d}
    [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]
    (bu : Basis a ℂ U) (bv : Basis b ℂ V)
    (bu' : Basis c ℂ U') (bv' : Basis d ℂ V')
    (f₁ f₂ : U →ₗ[ℂ] V) (g₁ g₂ : U' →ₗ[ℂ] V'),
    R.readout () ()
      (finrank ℂ (LinearMap.range (TensorProduct.map f₁ g₁ + TensorProduct.map f₂ g₂)))
      (tensorSum (LinearMap.toMatrix bu bv f₁) (LinearMap.toMatrix bu bv f₂)
        (LinearMap.toMatrix bu' bv' g₁) (LinearMap.toMatrix bu' bv' g₂)).rank

private theorem rejected_law : ¬ arena.{u,v,w,z,a,b,c,d}.Law natRejected := by
  intro h
  exact @h PUnit.{u+1} PUnit.{v+1} PUnit.{w+1} PUnit.{z+1}
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    PEmpty.{a+1} PEmpty.{b+1} PEmpty.{c+1} PEmpty.{d+1}
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (Basis.empty _) (Basis.empty _) (Basis.empty _) (Basis.empty _) 0 0 0 0

def source_registration : Registration arena.{u,v,w,z,a,b,c,d} (type_of% @finrank_tensorSum_toMatrix) where
  actual := natActual
  bridge := Iff.rfl
  variation := ⟨@finrank_tensorSum_toMatrix, natRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law natActual natRejected rejected_law
  dependence := natDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@finrank_tensorSum_toMatrix) (Realization natSignature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.finrank_tensorSum_toMatrix.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.SufficiencyAux.CoordinateRank.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z,a,b,c,d}⟩
  objectArena := .source ⟨arena.{u,v,w,z,a,b,c,d}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z,a,b,c,d} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature natActual.readout natActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PartialTransposeSaturation.Sufficiency
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[ "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn" ]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end CoordinateRank


end Reg.D5.S3.Quantum.Entanglement.PartialTransposeSaturation.SufficiencyAux
