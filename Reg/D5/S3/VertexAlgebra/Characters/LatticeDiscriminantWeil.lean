import Reg.D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
open LeanInformationAudit Matrix
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeDiscriminantTheta
open _root_.D5.S3.VertexAlgebra.LatticeDiscriminantWeil
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.VertexAlgebra.LatticeDiscriminantTheta
open private zeroLattice zeroPositive equalityDependence
  from Reg.D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

namespace Reg.D5.S3.VertexAlgebra.LatticeDiscriminantWeil

namespace SectorS
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData) (hD : (gramReal D).PosDef)
    (a₀ : Discriminant D) (τ : ℂ) (hτ : 0 < τ.im),
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    letI : Fintype (Discriminant D) := Fintype.ofFinite _
    a.readout () ℂ (sectorTheta D a₀ (-1/τ))
      ((-Complex.I*τ) ^ ((D.rank : ℂ)/2) / (Real.sqrt (gramReal D).det : ℂ) *
        ∑ c : Discriminant D, pairingCharacter D hD a₀ (-c) * sectorTheta D c τ)

private theorem sourceBridge : (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.sector_S)) ↔ arena.Law equalityActual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact h zeroLattice zeroPositive 0 Complex.I (by simp)

def family : Registration arena (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.sector_S)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp sector_S, equalityRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.sector_S) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.SectorS.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.SectorS.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature equalityActual.readout equalityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SectorS

namespace FiniteWeil
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData) (hD : Fact (gramReal D).PosDef),
    letI : Fact (gramReal D).PosDef := hD
    rho D ≠ 0 ∧
    a.readout () ℂ (rho D * rho D) (Nat.card (Discriminant D) : ℂ) ∧
    a.readout () ((Discriminant D → ℂ) →ₗ[ℂ] (Discriminant D → ℂ))
      ((weilS D).comp (weilS D)) (chargeConjugation D) ∧
    a.readout () ((Discriminant D → ℂ) →ₗ[ℂ] (Discriminant D → ℂ))
      ((weilS D).comp ((weilS D).comp ((weilS D).comp (weilS D)))) LinearMap.id ∧
    a.readout () ((Discriminant D → ℂ) →ₗ[ℂ] (Discriminant D → ℂ))
      ((weilS D).comp (weilSplus D)) LinearMap.id ∧
    a.readout () ((Discriminant D → ℂ) →ₗ[ℂ] (Discriminant D → ℂ))
      ((weilSplus D).comp (weilS D)) LinearMap.id ∧
    a.readout () ((Discriminant D → ℂ) →ₗ[ℂ] (Discriminant D → ℂ))
      (((weilS D).comp (weilT D)).comp
        (((weilS D).comp (weilT D)).comp ((weilS D).comp (weilT D))))
      (gaussPhase D • chargeConjugation D)

private theorem sourceBridge : (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.finite_weil_relations)) ↔ arena.Law equalityActual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact (h zeroLattice ⟨zeroPositive⟩).2.1

def family : Registration arena (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.finite_weil_relations)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp finite_weil_relations, equalityRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.finite_weil_relations) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.FiniteWeil.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.FiniteWeil.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature equalityActual.readout equalityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end FiniteWeil

namespace Milgram
abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData) (hD : (gramReal D).PosDef),
    letI : Fact (gramReal D).PosDef := ⟨hD⟩
    a.readout () ℂ (gaussPhase D) (Complex.exp (Real.pi * Complex.I * (D.rank : ℂ)/4))

private theorem sourceBridge : (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.milgram)) ↔ arena.Law equalityActual := Iff.rfl

private theorem rejectedLaw : ¬ arena.Law equalityRejected := by
  intro h
  exact h zeroLattice zeroPositive

def family : Registration arena (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.milgram)) where
  actual := equalityActual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp milgram, equalityRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      cases i
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.milgram) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.Milgram.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeDiscriminantWeil.Milgram.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize equalitySignature equalityActual.readout equalityActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.LatticeDiscriminantWeil
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Milgram

end Reg.D5.S3.VertexAlgebra.LatticeDiscriminantWeil
