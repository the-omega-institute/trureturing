import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockCharacter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Complex
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockGradedTrace
open LatticeHalfFockChargedTensorCoefficients TwistedGround.OperatorAlgebra
open LatticeTwistedGroundRealization LatticeTwistedGroundRealization.SignQuotient
open HalfFockSpectralFiberSource
open _root_.D5.S3.Combinatorics.Partitions
open ColouredOddOccupation AnalyticOddOccupation EtaOddOccupation
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCharacter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCharacter

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h

private def emptyLattice : LatticeData where
  rank := 0
  G := 1
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

private theorem empty_unit : IsUnit emptyLattice.G.det := by
  simp [emptyLattice]

namespace Series

abbrev arena : Arena where
  signature := signature
  Law a := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) (q : ℂ) (hq : ‖q‖ < 1),
    (∀ N, a.readout () () (actualTraceTerm D hu A q N)
      ((ColouredOddMultiplicity.partitionCount D.rank N : ℂ) *
        LinearMap.trace ℂ (ActualGround D hu) A * q ^ N)) ∧
    Summable (fun N : ℕ => ‖actualTraceTerm D hu A q N‖) ∧
    HasSum (actualTraceTerm D hu A q)
      (LinearMap.trace ℂ (ActualGround D hu) A * oddCoefficientSeries D.rank q)

private theorem source_bridge :
    (type_of% (@D5.S3.VertexAlgebra.LatticeHalfFockCharacter.actual_trace_series)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h emptyLattice empty_unit 0 0 (by norm_num)).1 0

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeHalfFockCharacter.actual_trace_series)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp actual_trace_series, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeHalfFockCharacter.actual_trace_series) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockCharacter.Series.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockCharacter.Series.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Series

namespace Modular

abbrev arena : Arena where
  signature := signature
  Law a := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) (τ : ℂ) (hτ : 0 < τ.im),
    Summable (fun N : ℕ => ‖exp (2 * Real.pi * I * τ * D.rank / 48) *
      actualTraceTerm D hu A (exp (Real.pi * I * τ)) N‖) ∧
    HasSum (fun N : ℕ => exp (2 * Real.pi * I * τ * D.rank / 48) *
      actualTraceTerm D hu A (exp (Real.pi * I * τ)) N)
      (LinearMap.trace ℂ (ActualGround D hu) A *
        (ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ D.rank) ∧
    a.readout () () (actualInsertedCharacter D hu A τ)
      (LinearMap.trace ℂ (ActualGround D hu) A *
        (ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ D.rank) ∧
    (∀ m : ℕ, D.rank = 2 * m → actualInsertedCharacter D hu A (-1 / τ) =
      LinearMap.trace ℂ (ActualGround D hu) A * ((2 : ℂ) ^ m)⁻¹ *
        (ModularForm.eta τ / ModularForm.eta (2 * τ)) ^ (2 * m)) ∧
    (∀ (x : Extension D ⧸ K D), quotientCharge D x ≠ 0 →
      A = groundRepresentation D hu x →
      (∀ N, actualTraceTerm D hu A (exp (Real.pi * I * τ)) N = 0) ∧
      HasSum (fun N : ℕ => exp (2 * Real.pi * I * τ * D.rank / 48) *
        actualTraceTerm D hu A (exp (Real.pi * I * τ)) N) 0 ∧
      actualInsertedCharacter D hu A τ = 0)

private theorem source_bridge :
    (type_of% (@D5.S3.VertexAlgebra.LatticeHalfFockCharacter.actual_character_modular)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h emptyLattice empty_unit 0 I (by norm_num)).2.2.1

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.LatticeHalfFockCharacter.actual_character_modular)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp actual_character_modular, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.LatticeHalfFockCharacter.actual_character_modular) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockCharacter.Modular.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockCharacter.Modular.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Modular

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCharacter

#print axioms Reg.D5.S3.VertexAlgebra.LatticeHalfFockCharacter.Series.family

#print axioms Reg.D5.S3.VertexAlgebra.LatticeHalfFockCharacter.Series.audit

#print axioms Reg.D5.S3.VertexAlgebra.LatticeHalfFockCharacter.Modular.family

#print axioms Reg.D5.S3.VertexAlgebra.LatticeHalfFockCharacter.Modular.audit
