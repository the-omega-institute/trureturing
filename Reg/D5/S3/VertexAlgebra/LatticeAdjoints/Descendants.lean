import D5.S3.VertexAlgebra.LatticeAdjoints.Descendants
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.LatticeAdjoints.Descendants

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy
open LatticeSugawaraCurrents LatticeOppositeCoefficients LatticeChargedFockForms
open LatticeOscillatorFockForm LatticeAdjoints.Descendants
open scoped BigOperators VertexOperator

noncomputable section

private def emptyLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro axis; exact Fin.elim0 axis
  even_diagonal := by intro axis; exact Fin.elim0 axis

private theorem emptyHG : (0 : Matrix (Fin emptyLattice.rank) (Fin emptyLattice.rank) ℂ) *
    gramComplex emptyLattice = 1 := by
  exact funext fun axis => Fin.elim0 axis

private theorem emptyGH : gramComplex emptyLattice *
    (0 : Matrix (Fin emptyLattice.rank) (Fin emptyLattice.rank) ℂ) = 1 := by
  exact funext fun axis => Fin.elim0 axis

private theorem hermitianVacuum (data : LatticeData) :
    hermitianForm data (vacuum data) (vacuum data) = 1 := by
  simp [hermitianForm, vacuum, Finsupp.lsum_single, fockForm_vacuum_left]

private theorem pctVacuum (data : LatticeData) : pct data (vacuum data) = vacuum data := by
  simp [pct, coefficientConjugation, conjugatePolynomial, vacuum]

private theorem bpzVacuum (data : LatticeData) :
    bpzForm data (vacuum data) (vacuum data) = 1 := by
  change hermitianForm data (pct data (vacuum data)) (vacuum data) = 1
  rw [pctVacuum, hermitianVacuum]

namespace BPZHomogeneous

abbrev Parameters := LatticeData

abbrev signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := VertexOperator ℂ (Carrier parameter)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ parameter state => Y parameter state)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ parameter state => actual.readout () parameter state + Y parameter (vacuum parameter))
  (fun empty => nomatch empty)

def law (realization : Realization signature) : Prop := ∀ (data : LatticeData)
    (matrix : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (leftInverse : matrix * gramComplex data = 1)
    (rightInverse : gramComplex data * matrix = 1)
    (state left right : Carrier data) (weight index : ℤ)
    (homogeneous : state ∈ grade data weight),
    bpzForm data (((realization.readout () data state)[[index]]) left) right =
      bpzForm data left (oppositeCoeff data matrix weight state index right)

abbrev arena : Arena where
  signature := signature
  Law := law

private def zeroParameters : Parameters := emptyLattice

abbrev SourceStatement := ∀ (data : LatticeData)
    (matrix : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (leftInverse : matrix * gramComplex data = 1)
    (rightInverse : gramComplex data * matrix = 1)
    (state left right : Carrier data) (weight : ℤ) (index : ℤ) (homogeneous : state ∈ grade data weight),
    bpzForm data (((Y data state)[[index]]) left) right =
      bpzForm data left (oppositeCoeff data matrix weight state index right)

private theorem sourceBridge : SourceStatement ↔ arena.Law actual := Iff.rfl

private theorem actualLaw : arena.Law actual := sourceBridge.mp bpz_stateField_homogeneous

private theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  have good := actualLaw emptyLattice 0 emptyHG emptyGH 0 (vacuum emptyLattice) (vacuum emptyLattice) 0 (-1) (Submodule.zero_mem _)
  have bad := law emptyLattice 0 emptyHG emptyGH 0 (vacuum emptyLattice) (vacuum emptyLattice) 0 (-1) (Submodule.zero_mem _)
  change bpzForm emptyLattice
    (((Y emptyLattice 0)[[-1]]) (vacuum emptyLattice)) (vacuum emptyLattice) = _ at good
  change bpzForm emptyLattice
    (((Y emptyLattice 0 + Y emptyLattice (vacuum emptyLattice))[[-1]])
      (vacuum emptyLattice)) (vacuum emptyLattice) = _ at bad
  rw [map_zero, zero_add, stateField_creation] at bad
  simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, bpzVacuum] at good bad
  exact zero_ne_one (good.trans bad.symm)

private theorem actualDependence :
    actual.readout () zeroParameters (vacuum emptyLattice) ≠
      actual.readout () zeroParameters 0 := by
  intro equality
  have impossible := congrArg (fun field : VertexOperator ℂ (Carrier emptyLattice) =>
    ((field)[[-1]]) (vacuum emptyLattice)) equality
  change (((Y emptyLattice (vacuum emptyLattice))[[-1]]) (vacuum emptyLattice)) =
    (((Y emptyLattice 0)[[-1]]) (vacuum emptyLattice)) at impossible
  rw [stateField_creation] at impossible
  simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply] at impossible
  exact vacuum_nonzero emptyLattice impossible

def sourceWitness : Registration arena SourceStatement where
  actual := actual
  bridge := sourceBridge
  variation := ⟨actualLaw, rejected, rejectedFails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedFails
  dependence := by
    intro role
    exact ⟨zeroParameters, (vacuum emptyLattice),
      0, actualDependence⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.bpz_stateField_homogeneous)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.bpz_stateField_homogeneous.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.BPZHomogeneous.sourceWitness
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeAdjoints.Descendants
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `backward.isDefEq.respectTransparency, value := .bool false }]

end BPZHomogeneous

namespace HermitianHomogeneous

abbrev Parameters := LatticeData

abbrev signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := VertexOperator ℂ (Carrier parameter)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ parameter state => Y parameter state)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ parameter state => actual.readout () parameter state + Y parameter (vacuum parameter))
  (fun empty => nomatch empty)

def law (realization : Realization signature) : Prop := ∀ (data : LatticeData)
    (matrix : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (leftInverse : matrix * gramComplex data = 1)
    (rightInverse : gramComplex data * matrix = 1)
    (state left right : Carrier data) (weight index : ℤ)
    (homogeneous : state ∈ grade data weight),
    hermitianForm data (((realization.readout () data state)[[index]]) left) right =
      hermitianForm data left (oppositeCoeff data matrix weight (pct data state) index right)

abbrev arena : Arena where
  signature := signature
  Law := law

private def zeroParameters : Parameters := emptyLattice

abbrev SourceStatement := ∀ (data : LatticeData)
    (matrix : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (leftInverse : matrix * gramComplex data = 1)
    (rightInverse : gramComplex data * matrix = 1)
    (state left right : Carrier data) (weight : ℤ) (index : ℤ) (homogeneous : state ∈ grade data weight),
    hermitianForm data (((Y data state)[[index]]) left) right =
      hermitianForm data left (oppositeCoeff data matrix weight (pct data state) index right)

private theorem sourceBridge : SourceStatement ↔ arena.Law actual := Iff.rfl

private theorem actualLaw : arena.Law actual := sourceBridge.mp hermitian_stateField_homogeneous

private theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  have good := actualLaw emptyLattice 0 emptyHG emptyGH 0 (vacuum emptyLattice) (vacuum emptyLattice) 0 (-1) (Submodule.zero_mem _)
  have bad := law emptyLattice 0 emptyHG emptyGH 0 (vacuum emptyLattice) (vacuum emptyLattice) 0 (-1) (Submodule.zero_mem _)
  change hermitianForm emptyLattice
    (((Y emptyLattice 0)[[-1]]) (vacuum emptyLattice)) (vacuum emptyLattice) = _ at good
  change hermitianForm emptyLattice
    (((Y emptyLattice 0 + Y emptyLattice (vacuum emptyLattice))[[-1]])
      (vacuum emptyLattice)) (vacuum emptyLattice) = _ at bad
  rw [map_zero, zero_add, stateField_creation] at bad
  simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, hermitianVacuum] at good bad
  exact zero_ne_one (good.trans bad.symm)

private theorem actualDependence :
    actual.readout () zeroParameters (vacuum emptyLattice) ≠
      actual.readout () zeroParameters 0 := by
  intro equality
  have impossible := congrArg (fun field : VertexOperator ℂ (Carrier emptyLattice) =>
    ((field)[[-1]]) (vacuum emptyLattice)) equality
  change (((Y emptyLattice (vacuum emptyLattice))[[-1]]) (vacuum emptyLattice)) =
    (((Y emptyLattice 0)[[-1]]) (vacuum emptyLattice)) at impossible
  rw [stateField_creation] at impossible
  simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply] at impossible
  exact vacuum_nonzero emptyLattice impossible

def sourceWitness : Registration arena SourceStatement where
  actual := actual
  bridge := sourceBridge
  variation := ⟨actualLaw, rejected, rejectedFails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedFails
  dependence := by
    intro role
    exact ⟨zeroParameters, (vacuum emptyLattice),
      0, actualDependence⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.hermitian_stateField_homogeneous)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.hermitian_stateField_homogeneous.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.HermitianHomogeneous.sourceWitness
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeAdjoints.Descendants
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `backward.isDefEq.respectTransparency, value := .bool false }]

end HermitianHomogeneous

namespace BPZMixed

abbrev Parameters := LatticeData

abbrev signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := VertexOperator ℂ (Carrier parameter)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ parameter state => Y parameter state)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ parameter state => actual.readout () parameter state + Y parameter (vacuum parameter))
  (fun empty => nomatch empty)

def law (realization : Realization signature) : Prop := ∀ (data : LatticeData)
    (matrix : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (leftInverse : matrix * gramComplex data = 1)
    (rightInverse : gramComplex data * matrix = 1)
    (state left right : Carrier data) (index : ℤ),
    bpzForm data (((realization.readout () data state)[[index]]) left) right =
      ∑ weight ∈ stateEnergies data state,
        bpzForm data left (oppositeCoeff data matrix weight (gradeProjection data weight state) index right)

abbrev arena : Arena where
  signature := signature
  Law := law

private def zeroParameters : Parameters := emptyLattice

abbrev SourceStatement := ∀ (data : LatticeData)
    (matrix : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (leftInverse : matrix * gramComplex data = 1)
    (rightInverse : gramComplex data * matrix = 1)
    (state left right : Carrier data) (index : ℤ),
    bpzForm data (((Y data state)[[index]]) left) right =
      ∑ weight ∈ stateEnergies data state,
      bpzForm data left (oppositeCoeff data matrix weight (gradeProjection data weight state) index right)

private theorem sourceBridge : SourceStatement ↔ arena.Law actual := Iff.rfl

private theorem actualLaw : arena.Law actual := sourceBridge.mp bpz_stateField_all

private theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  have good := actualLaw emptyLattice 0 emptyHG emptyGH 0 (vacuum emptyLattice) (vacuum emptyLattice) (-1)
  have bad := law emptyLattice 0 emptyHG emptyGH 0 (vacuum emptyLattice) (vacuum emptyLattice) (-1)
  change bpzForm emptyLattice
    (((Y emptyLattice 0)[[-1]]) (vacuum emptyLattice)) (vacuum emptyLattice) = _ at good
  change bpzForm emptyLattice
    (((Y emptyLattice 0 + Y emptyLattice (vacuum emptyLattice))[[-1]])
      (vacuum emptyLattice)) (vacuum emptyLattice) = _ at bad
  rw [map_zero, zero_add, stateField_creation] at bad
  simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, bpzVacuum] at good bad
  exact zero_ne_one (good.trans bad.symm)

private theorem actualDependence :
    actual.readout () zeroParameters (vacuum emptyLattice) ≠
      actual.readout () zeroParameters 0 := by
  intro equality
  have impossible := congrArg (fun field : VertexOperator ℂ (Carrier emptyLattice) =>
    ((field)[[-1]]) (vacuum emptyLattice)) equality
  change (((Y emptyLattice (vacuum emptyLattice))[[-1]]) (vacuum emptyLattice)) =
    (((Y emptyLattice 0)[[-1]]) (vacuum emptyLattice)) at impossible
  rw [stateField_creation] at impossible
  simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply] at impossible
  exact vacuum_nonzero emptyLattice impossible

def sourceWitness : Registration arena SourceStatement where
  actual := actual
  bridge := sourceBridge
  variation := ⟨actualLaw, rejected, rejectedFails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedFails
  dependence := by
    intro role
    exact ⟨zeroParameters, (vacuum emptyLattice),
      0, actualDependence⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.bpz_stateField_all)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.bpz_stateField_all.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.BPZMixed.sourceWitness
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeAdjoints.Descendants
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `backward.isDefEq.respectTransparency, value := .bool false }]

end BPZMixed

namespace HermitianMixed

abbrev Parameters := LatticeData

abbrev signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := VertexOperator ℂ (Carrier parameter)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ parameter state => Y parameter state)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ parameter state => actual.readout () parameter state + Y parameter (vacuum parameter))
  (fun empty => nomatch empty)

def law (realization : Realization signature) : Prop := ∀ (data : LatticeData)
    (matrix : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (leftInverse : matrix * gramComplex data = 1)
    (rightInverse : gramComplex data * matrix = 1)
    (state left right : Carrier data) (index : ℤ),
    hermitianForm data (((realization.readout () data state)[[index]]) left) right =
      ∑ weight ∈ stateEnergies data state,
        hermitianForm data left (oppositeCoeff data matrix weight (pct data (gradeProjection data weight state)) index right)

abbrev arena : Arena where
  signature := signature
  Law := law

private def zeroParameters : Parameters := emptyLattice

abbrev SourceStatement := ∀ (data : LatticeData)
    (matrix : Matrix (Fin data.rank) (Fin data.rank) ℂ)
    (leftInverse : matrix * gramComplex data = 1)
    (rightInverse : gramComplex data * matrix = 1)
    (state left right : Carrier data) (index : ℤ),
    hermitianForm data (((Y data state)[[index]]) left) right =
      ∑ weight ∈ stateEnergies data state,
      hermitianForm data left (oppositeCoeff data matrix weight (pct data (gradeProjection data weight state)) index right)

private theorem sourceBridge : SourceStatement ↔ arena.Law actual := Iff.rfl

private theorem actualLaw : arena.Law actual := sourceBridge.mp hermitian_stateField_all

private theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  have good := actualLaw emptyLattice 0 emptyHG emptyGH 0 (vacuum emptyLattice) (vacuum emptyLattice) (-1)
  have bad := law emptyLattice 0 emptyHG emptyGH 0 (vacuum emptyLattice) (vacuum emptyLattice) (-1)
  change hermitianForm emptyLattice
    (((Y emptyLattice 0)[[-1]]) (vacuum emptyLattice)) (vacuum emptyLattice) = _ at good
  change hermitianForm emptyLattice
    (((Y emptyLattice 0 + Y emptyLattice (vacuum emptyLattice))[[-1]])
      (vacuum emptyLattice)) (vacuum emptyLattice) = _ at bad
  rw [map_zero, zero_add, stateField_creation] at bad
  simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, hermitianVacuum] at good bad
  exact zero_ne_one (good.trans bad.symm)

private theorem actualDependence :
    actual.readout () zeroParameters (vacuum emptyLattice) ≠
      actual.readout () zeroParameters 0 := by
  intro equality
  have impossible := congrArg (fun field : VertexOperator ℂ (Carrier emptyLattice) =>
    ((field)[[-1]]) (vacuum emptyLattice)) equality
  change (((Y emptyLattice (vacuum emptyLattice))[[-1]]) (vacuum emptyLattice)) =
    (((Y emptyLattice 0)[[-1]]) (vacuum emptyLattice)) at impossible
  rw [stateField_creation] at impossible
  simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply] at impossible
  exact vacuum_nonzero emptyLattice impossible

def sourceWitness : Registration arena SourceStatement where
  actual := actual
  bridge := sourceBridge
  variation := ⟨actualLaw, rejected, rejectedFails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedFails
  dependence := by
    intro role
    exact ⟨zeroParameters, (vacuum emptyLattice),
      0, actualDependence⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.hermitian_stateField_all)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.hermitian_stateField_all.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.HermitianMixed.sourceWitness
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeAdjoints.Descendants
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `backward.isDefEq.respectTransparency, value := .bool false }]

end HermitianMixed

namespace PCTGrading

abbrev Parameters := Σ data : LatticeData, ℤ

abbrev signature : Signature where
  Params := Parameters
  State parameter := Carrier parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Carrier parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ parameter state => pct parameter.1 state)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ parameter state => actual.readout () parameter state + vacuum parameter.1)
  (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law realization := ∀ (data : LatticeData) (state : Carrier data) (weight : ℤ)
    (homogeneous : state ∈ grade data weight),
    realization.readout () ⟨data, weight⟩ state ∈ grade data weight

abbrev SourceStatement := ∀ (data : LatticeData) (state : Carrier data) (weight : ℤ),
  state ∈ grade data weight → pct data state ∈ grade data weight

private theorem sourceBridge : SourceStatement ↔ arena.Law actual := Iff.rfl

private theorem actualLaw : arena.Law actual := sourceBridge.mp pct_grade

private theorem vacuumOutside : vacuum emptyLattice ∉ grade emptyLattice 1 := by
  intro member
  have vanishing := (mem_grade_iff emptyLattice 1 (vacuum emptyLattice)).mp member
    (0, 0) (by simp [energy, oscillatorEnergy])
  simpa [vacuum] using vanishing

private theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  have bad := law emptyLattice 0 1 (Submodule.zero_mem _)
  change pct emptyLattice 0 + vacuum emptyLattice ∈ grade emptyLattice 1 at bad
  rw [map_zero, zero_add] at bad
  exact vacuumOutside bad

private theorem actualDependence : actual.readout () ⟨emptyLattice, 0⟩ (vacuum emptyLattice) ≠
    actual.readout () ⟨emptyLattice, 0⟩ 0 := by
  change pct emptyLattice (vacuum emptyLattice) ≠ pct emptyLattice 0
  rw [pctVacuum, map_zero]
  exact vacuum_nonzero emptyLattice

def sourceWitness : Registration arena SourceStatement where
  actual := actual
  bridge := sourceBridge
  variation := ⟨actualLaw, rejected, rejectedFails⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedFails
  dependence := by
    intro role
    exact ⟨⟨emptyLattice, 0⟩, vacuum emptyLattice, 0, actualDependence⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.pct_grade)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.pct_grade.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeAdjoints.Descendants.PCTGrading.sourceWitness
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ parameter state => pct parameter.1 state)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeAdjoints.Descendants
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `backward.isDefEq.respectTransparency, value := .bool false }]

end PCTGrading

end
end Reg.D5.S3.VertexAlgebra.LatticeAdjoints.Descendants
