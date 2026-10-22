import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass
open _root_.D5.S3.VertexAlgebra.BcGhostFockSupport
open scoped TensorProduct

namespace Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass

noncomputable section

private def probeLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro first second; simp
  even_diagonal := by intro axis; exact Fin.elim0 axis

private theorem probe_Q_nonzero :
    Q probeLattice 0 (B probeLattice (-2) (vacuumVector probeLattice)) ≠ 0 := by
  intro vanishing
  have matterZero : M probeLattice 0 (-2) (vacuumVector probeLattice) = 0 := by
    simp [M, sugawaraMode, sugawaraField]
  have ward := congrArg
    (fun operator : Module.End ℂ (State probeLattice) => operator (vacuumVector probeLattice))
    (ward_identity probeLattice 0 (-2))
  have stressZero : G probeLattice (-2) (vacuumVector probeLattice) = 0 := by
    simpa only [LinearMap.add_apply, Module.End.mul_apply, vanishing,
      vacuum_closed, map_zero, matterZero, add_zero, zero_add] using ward.symm
  have contraction :
      G probeLattice 2 (G probeLattice (-2) (vacuumVector probeLattice)) =
        (-13 : ℂ) • vacuumVector probeLattice := by
    simp only [G, vacuumVector, TensorProduct.map_tmul, LinearMap.id_apply]
    rw [_root_.D5.S3.VertexAlgebra.BcGhostVacuum.L_vacuum_contraction
      (K := ℂ) 2 (by norm_num)]
    norm_num [TensorProduct.tmul_smul, TensorProduct.tmul_neg]
  have detected := congrArg
    (fun state : State probeLattice => epsilon probeLattice (G probeLattice 2 state)) stressZero
  rw [contraction] at detected
  simp only [map_smul, RingHom.id_apply, epsilon_vacuum, map_zero,
    smul_eq_mul, mul_one] at detected
  norm_num at detected

abbrev tensorSignature : Signature where
  Params := Σ lattice : LatticeData, Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  State parameter := State parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := State parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def qActual : Realization tensorSignature :=
  realize tensorSignature (fun _ parameter state => Q parameter.1 parameter.2 state)
    (fun empty => nomatch empty)

def vacuumReplacement : Realization tensorSignature :=
  realize tensorSignature (fun _ parameter _ => vacuumVector parameter.1)
    (fun empty => nomatch empty)

private theorem qDependence : ObservationalDependence tensorSignature qActual := by
  intro role
  refine ⟨⟨probeLattice, 0⟩,
    B probeLattice (-2) (vacuumVector probeLattice), 0, ?_⟩
  intro equality
  apply probe_Q_nonzero
  simpa [qActual, realize] using equality

abbrev coefficientSignature : Signature where
  Params := Σ lattice : LatticeData, Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  State parameter := State parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def coefficientActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ parameter state => epsilon parameter.1 state)
    (fun empty => nomatch empty)

def oneReplacement : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ => 1) (fun empty => nomatch empty)

private theorem coefficientDependence :
    ObservationalDependence coefficientSignature coefficientActual := by
  intro role
  refine ⟨⟨probeLattice, 0⟩, vacuumVector probeLattice, 0, ?_⟩
  simpa [coefficientActual, realize, epsilon_vacuum] using (one_ne_zero : (1 : ℂ) ≠ 0)

namespace Closed

abbrev arena : Arena where
  signature := tensorSignature
  Law readout := ∀ (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ),
    readout.readout () ⟨lattice, matrix⟩ (vacuumVector lattice) = 0

def statement : Prop := ∀ (lattice : LatticeData)
  (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ),
  Q lattice matrix (vacuumVector lattice) = 0

theorem sourceReconstruction : statement ↔ arena.Law qActual := Iff.rfl

theorem actualPositive : arena.Law qActual := vacuum_closed

theorem rejected : ¬ arena.Law vacuumReplacement := by
  intro law
  have vanishing := law probeLattice 0
  change vacuumVector probeLattice = 0 at vanishing
  have detected := congrArg
    (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.epsilon probeLattice) vanishing
  exact (one_ne_zero : (1 : ℂ) ≠ 0)
    (by simpa only [epsilon_vacuum, map_zero] using detected)

def source : Registration arena statement where
  actual := qActual
  bridge := sourceReconstruction
  variation := ⟨actualPositive, vacuumReplacement, rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨vacuumReplacement, ?_, rfl, rejected⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := qDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.vacuum_closed)
    (type_of% qActual) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.Closed.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.Closed.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tensorSignature qActual.readout qActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Closed

namespace Coefficient

abbrev arena : Arena where
  signature := coefficientSignature
  Law readout := ∀ (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ) (state : State lattice),
    readout.readout () ⟨lattice, matrix⟩ (Q lattice matrix state) = 0

def statement : Prop := ∀ (lattice : LatticeData)
  (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ) (state : State lattice),
  epsilon lattice (Q lattice matrix state) = 0

theorem sourceReconstruction : statement ↔ arena.Law coefficientActual := Iff.rfl

theorem actualPositive : arena.Law coefficientActual := epsilon_Q

theorem rejected : ¬ arena.Law oneReplacement := by
  intro law
  have impossible := law probeLattice 0 0
  exact (one_ne_zero : (1 : ℂ) ≠ 0) impossible

def source : Registration arena statement where
  actual := coefficientActual
  bridge := sourceReconstruction
  variation := ⟨actualPositive, oneReplacement, rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨oneReplacement, ?_, rfl, rejected⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := coefficientDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.epsilon_Q)
    (type_of% coefficientActual) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.Coefficient.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.Coefficient.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature coefficientActual.readout coefficientActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Coefficient

namespace Normalization

abbrev signature : Signature where
  Params := LatticeData
  State lattice := State lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ lattice state => epsilon lattice state)
    (fun empty => nomatch empty)

def zeroReplacement : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ lattice : LatticeData,
    readout.readout () lattice (vacuumVector lattice) = 1

def statement : Prop := ∀ lattice : LatticeData, epsilon lattice (vacuumVector lattice) = 1

theorem sourceReconstruction : statement ↔ arena.Law actual := Iff.rfl

theorem actualPositive : arena.Law actual := epsilon_vacuum

theorem rejected : ¬ arena.Law zeroReplacement := by
  intro law
  have impossible := law probeLattice
  exact (zero_ne_one : (0 : ℂ) ≠ 1) impossible

def source : Registration arena statement where
  actual := actual
  bridge := sourceReconstruction
  variation := ⟨actualPositive, zeroReplacement, rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨zeroReplacement, ?_, rfl, rejected⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨probeLattice, vacuumVector probeLattice, 0, ?_⟩
    simpa [actual, realize, epsilon_vacuum] using (one_ne_zero : (1 : ℂ) ≠ 0)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.epsilon_vacuum)
    (type_of% actual) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.Normalization.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.Normalization.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Normalization

namespace Nonexact

abbrev arena : Arena where
  signature := tensorSignature
  Law readout := ∀ (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ),
    ∀ state : State lattice,
      readout.readout () ⟨lattice, matrix⟩ state ≠ vacuumVector lattice

def statement : Prop := ∀ (lattice : LatticeData)
  (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ),
  vacuumVector lattice ∉ LinearMap.range (Q lattice matrix)

theorem sourceReconstruction : statement ↔ arena.Law qActual := by
  constructor
  · intro source lattice matrix state equality
    exact source lattice matrix (LinearMap.mem_range.mpr ⟨state, equality⟩)
  · intro law lattice matrix member
    obtain ⟨state, equality⟩ := LinearMap.mem_range.mp member
    exact law lattice matrix state equality

theorem actualPositive : arena.Law qActual := sourceReconstruction.mp vacuum_not_mem_range

theorem rejected : ¬ arena.Law vacuumReplacement := by
  intro law
  exact law probeLattice 0 0 rfl

def source : Registration arena statement where
  actual := qActual
  bridge := sourceReconstruction
  variation := ⟨actualPositive, vacuumReplacement, rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨vacuumReplacement, ?_, rfl, rejected⟩
      intro other distinct
      exact (distinct (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := qDependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.vacuum_not_mem_range)
    (type_of% qActual) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.Nonexact.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.Nonexact.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tensorSignature qActual.readout qActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Nonexact

#print axioms probe_Q_nonzero
#print axioms Closed.source
#print axioms Coefficient.source
#print axioms Normalization.source
#print axioms Nonexact.source

end

end Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass
