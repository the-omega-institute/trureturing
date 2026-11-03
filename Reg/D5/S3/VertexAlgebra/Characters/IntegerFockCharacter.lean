import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Characters.IntegerFockCharacter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators PowerSeries.WithPiTopology
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.IntegerFockCharacter

namespace Reg.D5.S3.VertexAlgebra.IntegerFockCharacter

abbrev natSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def natActual : Realization natSignature :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def natRejected : Realization natSignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem natDependence : ObservationalDependence natSignature natActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℕ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he

abbrev seriesSignature : Signature where
  Params := Unit
  State _ := PowerSeries ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := PowerSeries ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def seriesActual : Realization seriesSignature :=
  realize _ (fun _ _ x y => x = y) (fun e => nomatch e)
def seriesRejected : Realization seriesSignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem seriesDependence : ObservationalDependence seriesSignature seriesActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : PowerSeries ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  exact one_ne_zero he

namespace Cardinality
abbrev arena : Arena where
  signature := natSignature
  Law a := ∀ (r N : ℕ),
    a.readout () () (Nat.card (EnergyFiber r N))
      (∑ e ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N,
        ∏ i : Fin r, Nat.card (Nat.Partition (e i)))

private theorem bridge : (type_of% (@D5.S3.VertexAlgebra.IntegerFockCharacter.card_energyFiber)) ↔
    arena.Law natActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law natRejected := by
  intro h
  exact h 0 0 

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.IntegerFockCharacter.card_energyFiber)) where
  actual := natActual
  bridge := bridge
  variation := ⟨bridge.mp card_energyFiber, natRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := natDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.IntegerFockCharacter.card_energyFiber) (Realization natSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.IntegerFockCharacter.Cardinality.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.IntegerFockCharacter.Cardinality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature natActual.readout natActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.IntegerFockCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Cardinality

namespace Dimension
abbrev arena : Arena where
  signature := natSignature
  Law a := ∀ (r N : ℕ),
    a.readout () () (Module.finrank ℂ (grade r N)) (Nat.card (PartitionTuple r N))

private theorem bridge : (type_of% (@D5.S3.VertexAlgebra.IntegerFockCharacter.finrank_grade)) ↔
    arena.Law natActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law natRejected := by
  intro h
  exact h 0 0 

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.IntegerFockCharacter.finrank_grade)) where
  actual := natActual
  bridge := bridge
  variation := ⟨bridge.mp finrank_grade, natRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨natRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := natDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.IntegerFockCharacter.finrank_grade) (Realization natSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.IntegerFockCharacter.Dimension.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.IntegerFockCharacter.Dimension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature natActual.readout natActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.IntegerFockCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Dimension

namespace Convolution
abbrev arena : Arena where
  signature := seriesSignature
  Law a := ∀ (r : ℕ),
    a.readout () () (character r) (ordinaryPartitionSeries ^ r)

private theorem bridge : (type_of% (@D5.S3.VertexAlgebra.IntegerFockCharacter.character_eq_partition_power)) ↔
    arena.Law seriesActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law seriesRejected := by
  intro h
  exact h 0 

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.IntegerFockCharacter.character_eq_partition_power)) where
  actual := seriesActual
  bridge := bridge
  variation := ⟨bridge.mp character_eq_partition_power, seriesRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨seriesRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := seriesDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.IntegerFockCharacter.character_eq_partition_power) (Realization seriesSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.IntegerFockCharacter.Convolution.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.IntegerFockCharacter.Convolution.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seriesSignature seriesActual.readout seriesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.IntegerFockCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Convolution

namespace Euler
abbrev arena : Arena where
  signature := seriesSignature
  Law a := ∀ (r : ℕ),
    a.readout () () (character r)
      ((∏' n : ℕ, (1 - (PowerSeries.X : PowerSeries ℂ) ^ (n + 1))⁻¹) ^ r)

private theorem bridge : (type_of% (@D5.S3.VertexAlgebra.IntegerFockCharacter.character_euler_product)) ↔
    arena.Law seriesActual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law seriesRejected := by
  intro h
  exact h 0 

def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.IntegerFockCharacter.character_euler_product)) where
  actual := seriesActual
  bridge := bridge
  variation := ⟨bridge.mp character_euler_product, seriesRejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨seriesRejected, ?_, rfl, rejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := seriesDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.IntegerFockCharacter.character_euler_product) (Realization seriesSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.IntegerFockCharacter.Euler.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.IntegerFockCharacter.Euler.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seriesSignature seriesActual.readout seriesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Characters.IntegerFockCharacter
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Euler

end Reg.D5.S3.VertexAlgebra.IntegerFockCharacter
