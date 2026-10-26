import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockParityT

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockParityT

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockParityT
open scoped TensorProduct

noncomputable section

private def hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩

private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have hd : hyperbolic.G.det = -1 := by
    change Matrix.det (!![(0 : ℤ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) = -1
    norm_num [Matrix.det_fin_two]
  rw [hd]
  exact isUnit_neg_one

private def gradeOneIndex : ActualGradeIndex hyperbolic hyperbolic_unit 1 :=
  (⟨Finsupp.single ((0 : Fin 2), 0) 1, by
    simp [oddWeight, Finsupp.weight_single, omega]⟩, 0)

structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  N : ℕ

abbrev signature : Signature where
  Params := Params
  State p := actualGrade p.D p.hu p.N
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ActualTensor p.D p.hu
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p v => actualParity p.D p.hu (v : ActualTensor p.D p.hu))
  (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (N : ℕ)
    (v : actualGrade D hu N),
    readout.readout () ⟨D, hu, N⟩ v =
      ((-1 : ℂ) ^ N) • (v : ActualTensor D hu)

theorem actual_law : arena.Law actual := by
  intro D hu N v
  exact actualParity_on_actualGrade D hu N v

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h hyperbolic hyperbolic_unit 1
    (actualGradeBasis hyperbolic hyperbolic_unit 1 gradeOneIndex)
  have hn := (actualGradeBasis hyperbolic hyperbolic_unit 1).ne_zero gradeOneIndex
  have hz' : (0 : ActualTensor hyperbolic hyperbolic_unit) =
      (-1 : ℂ) • (actualGradeBasis hyperbolic hyperbolic_unit 1 gradeOneIndex :
        ActualTensor hyperbolic hyperbolic_unit) := by
    simpa [rejected, realize] using hz
  exact hn (by simpa using hz'.symm)

def familyRegistration : Registration arena (type_of% (@actualParity_on_actualGrade)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := by
    intro role
    refine ⟨⟨hyperbolic, hyperbolic_unit, 1⟩, 0,
      actualGradeBasis hyperbolic hyperbolic_unit 1 gradeOneIndex, ?_⟩
    intro h
    have hn := (actualGradeBasis hyperbolic hyperbolic_unit 1).ne_zero gradeOneIndex
    change actualParity hyperbolic hyperbolic_unit (0 : ActualTensor hyperbolic hyperbolic_unit) =
      actualParity hyperbolic hyperbolic_unit
        (actualGradeBasis hyperbolic hyperbolic_unit 1 gradeOneIndex :
          ActualTensor hyperbolic hyperbolic_unit) at h
    rw [map_zero, actualParity_on_grade_basis] at h
    simp only [pow_one, neg_smul] at h
    exact hn (by simpa using h.symm)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actualParity_on_actualGrade)
    (type_of% (realize signature actual.readout actual.anchor)) Type Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeHalfFockParityT.actualParity_on_actualGrade.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockParityT.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockParityT
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

#print axioms registration

namespace Analytic

open Complex
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockCharacter
open _root_.D5.S3.Combinatorics.Partitions.EtaOddOccupation

private def emptyLattice : LatticeData where
  rank := 0
  G := 1
  symmetric := by intro i; exact Fin.elim0 i
  even_diagonal := by intro i; exact Fin.elim0 i

private theorem empty_unit : IsUnit emptyLattice.G.det := by
  change IsUnit (Matrix.det (1 : Matrix (Fin 0) (Fin 0) ℤ))
  rw [Matrix.det_one]
  exact isUnit_one

abbrev equalitySignature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def equalityActual : Realization equalitySignature :=
  realize equalitySignature (fun _ _ x y => x = y) (fun e => nomatch e)

def equalityRejected : Realization equalitySignature :=
  realize equalitySignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem equalityDependence : ObservationalDependence equalitySignature equalityActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero h

abbrev sumSignature : Signature where
  Params := Unit
  State _ := ℕ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def sumActual : Realization sumSignature :=
  realize sumSignature (fun _ _ f s => HasSum f s) (fun e => nomatch e)

def sumRejected : Realization sumSignature :=
  realize sumSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem sumDependence : ObservationalDependence sumSignature sumActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun n => if n = 0 then 1 else 0), ?_⟩
  intro he
  have hz : HasSum (fun n : ℕ => if n = 0 then (1 : ℂ) else 0) 0 :=
    Eq.mp (congrFun he 0) hasSum_zero
  have ho : HasSum (fun n : ℕ => if n = 0 then (1 : ℂ) else 0) 1 :=
    hasSum_ite_eq 0 1
  exact zero_ne_one (hz.unique ho)

namespace TraceSeries

abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) (q : ℂ) (hq : ‖q‖ < 1),
    (∀ N, a.readout () () (actualParityTraceTerm D hu A q N)
      (actualTraceTerm D hu A (-q) N)) ∧
    Summable (fun N : ℕ => ‖actualParityTraceTerm D hu A q N‖) ∧
    HasSum (actualParityTraceTerm D hu A q)
      (LinearMap.trace ℂ (ActualGround D hu) A * oddCoefficientSeries D.rank (-q))

private theorem source_bridge :
    (type_of% (@actual_parity_trace_series)) ↔ arena.Law equalityActual := Iff.rfl

private theorem rejected_law : ¬ arena.Law equalityRejected := by
  intro h
  exact (h emptyLattice empty_unit 0 0 (by norm_num)).1 0

def family : Registration arena (type_of% (@actual_parity_trace_series)) where
  actual := equalityActual
  bridge := source_bridge
  variation := ⟨source_bridge.mp actual_parity_trace_series, equalityRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_parity_trace_series) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockParityT.Analytic.TraceSeries.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockParityT.Analytic.TraceSeries.family
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockParityT
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

#print axioms family
#print axioms audit

end TraceSeries

namespace CharacterSeries

abbrev arena : Arena where
  signature := sumSignature
  Law a := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) (τ : ℂ) (hτ : 0 < τ.im),
    Summable (fun N : ℕ => ‖exp (2 * Real.pi * I * τ * D.rank / 48) *
      actualParityTraceTerm D hu A (exp (Real.pi * I * τ)) N‖) ∧
    a.readout () () (fun N : ℕ => exp (2 * Real.pi * I * τ * D.rank / 48) *
      actualParityTraceTerm D hu A (exp (Real.pi * I * τ)) N)
      (actualParityInsertedCharacter D hu A τ)

private theorem source_bridge :
    (type_of% (@actual_parity_character_series)) ↔ arena.Law sumActual := Iff.rfl

private theorem rejected_law : ¬ arena.Law sumRejected := by
  intro h
  exact (h emptyLattice empty_unit 0 I (by norm_num)).2

def family : Registration arena (type_of% (@actual_parity_character_series)) where
  actual := sumActual
  bridge := source_bridge
  variation := ⟨source_bridge.mp actual_parity_character_series, sumRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨sumRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := sumDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_parity_character_series) (Realization sumSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockParityT.Analytic.CharacterSeries.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockParityT.Analytic.CharacterSeries.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sumSignature sumActual.readout sumActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockParityT
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end CharacterSeries

namespace PairedT

abbrev arena : Arena where
  signature := equalitySignature
  Law a := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (A : Module.End ℂ (ActualGround D hu)) (τ : ℂ) (hτ : 0 < τ.im),
    a.readout () () (actualInsertedCharacter D hu A (τ + 1))
      (exp (2 * Real.pi * I * D.rank / 48) * actualParityInsertedCharacter D hu A τ) ∧
    actualParityInsertedCharacter D hu A (τ + 1) =
      exp (2 * Real.pi * I * D.rank / 48) * actualInsertedCharacter D hu A τ ∧
    actualInsertedCharacter D hu A (τ + 2) =
      exp (2 * Real.pi * I * D.rank / 24) * actualInsertedCharacter D hu A τ ∧
    actualParityInsertedCharacter D hu A (τ + 2) =
      exp (2 * Real.pi * I * D.rank / 24) * actualParityInsertedCharacter D hu A τ

private theorem source_bridge :
    (type_of% (@actual_paired_T)) ↔ arena.Law equalityActual := Iff.rfl

private theorem rejected_law : ¬ arena.Law equalityRejected := by
  intro h
  exact (h emptyLattice empty_unit 0 I (by norm_num)).1

def family : Registration arena (type_of% (@actual_paired_T)) where
  actual := equalityActual
  bridge := source_bridge
  variation := ⟨source_bridge.mp actual_paired_T, equalityRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨equalityRejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      cases e
  dependence := equalityDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_paired_T) (Realization equalitySignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockParityT.Analytic.PairedT.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeHalfFockParityT.Analytic.PairedT.family
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
    owner := `D5.S3.VertexAlgebra.LatticeHalfFockParityT
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end PairedT


end Analytic

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockParityT
