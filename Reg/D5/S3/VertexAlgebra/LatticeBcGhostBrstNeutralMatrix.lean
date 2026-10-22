import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix
import D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass
open scoped BigOperators

namespace Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix

noncomputable section

abbrev signature : Signature where
  Params := Σ D : LatticeData, Matrix (Fin D.rank) (Fin D.rank) ℂ
  State parameter := Fin parameter.1.rank × State parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := State parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def expected (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (t : Fin D.rank) (tag : State D) : State D :=
  (∑ s : Fin D.rank,
      (neutralCoefficient D H s t - kronecker D s t) • kState D s) + tag

def actual : Realization signature :=
  realize signature
    (fun _ parameter state => Q parameter.1 parameter.2 (jState parameter.1 state.1) + state.2)
    (fun empty => nomatch empty)

def replacement : Realization signature :=
  realize signature
    (fun _ parameter state => expected parameter.1 parameter.2 state.1 state.2 +
      vacuumState parameter.1)
    (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (t : Fin D.rank)
    (tag : State D),
    readout.readout () ⟨D, H⟩ (t, tag) = expected D H t tag

def sourceStatement : Prop :=
  ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (t : Fin D.rank),
    Q D H (jState D t) =
      ∑ s : Fin D.rank,
        (neutralCoefficient D H s t - kronecker D s t) • kState D s

theorem sourceBridge : sourceStatement ↔ arena.Law actual := by
  constructor
  · intro source D H t tag
    simpa [actual, expected, realize, source D H t, add_assoc]
  · intro law D H t
    simpa [actual, expected, realize] using law D H t (0 : State D)

theorem actualPositive : arena.Law actual :=
  sourceBridge.mp Q_one_oscillator

private def probeLattice : LatticeData where
  rank := 1
  G := 0
  symmetric := by intro first second; simp
  even_diagonal := by intro axis; simp

private def probeIndex : Fin probeLattice.rank := ⟨0, by decide⟩

theorem rejected : ¬ arena.Law replacement := by
  intro law
  have equation := law probeLattice 0 probeIndex (0 : State probeLattice)
  change expected probeLattice 0 probeIndex 0 + vacuumState probeLattice =
    expected probeLattice 0 probeIndex 0 at equation
  have zero : vacuumState probeLattice = 0 := by
    calc
      vacuumState probeLattice =
          (expected probeLattice 0 probeIndex 0 + vacuumState probeLattice) -
            expected probeLattice 0 probeIndex 0 := by module
      _ = expected probeLattice 0 probeIndex 0 -
            expected probeLattice 0 probeIndex 0 := by
        rw [equation]
      _ = 0 := by module
  have detected := congrArg
    (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.epsilon probeLattice) zero
  simpa [vacuumState, epsilon_vacuum] using detected

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨probeLattice, 0⟩, (probeIndex, 0),
    (probeIndex, vacuumState probeLattice), ?_⟩
  intro equality
  have detected := congrArg
    (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.epsilon probeLattice) equality
  simp [actual, realize, vacuumState, epsilon_Q, epsilon_vacuum] at detected

def source : Registration arena sourceStatement where
  actual := actual
  bridge := sourceBridge
  variation := ⟨actualPositive, replacement, rejected⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      refine ⟨replacement, ?_, rfl, rejected⟩
      rintro ⟨⟩ distinct
      exact (distinct rfl).elim
    · intro empty
      exact Empty.elim empty
  dependence := dependence

def registration : Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix.Q_one_oscillator)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix.source
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev closedSignature : Signature where
  Params := Σ D : LatticeData, Matrix (Fin D.rank) (Fin D.rank) ℂ
  State parameter := State parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := State parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def closedExpected (D : LatticeData)
    (_H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (tag : State D) : State D := tag

def zActual : Realization closedSignature :=
  realize closedSignature
    (fun _ parameter state => Q parameter.1 parameter.2 (zState parameter.1) + state)
    (fun empty => nomatch empty)

def wActual : Realization closedSignature :=
  realize closedSignature
    (fun _ parameter state => Q parameter.1 parameter.2 (wState parameter.1) + state)
    (fun empty => nomatch empty)

def closedReplacement : Realization closedSignature :=
  realize closedSignature
    (fun _ parameter state => state + vacuumState parameter.1)
    (fun empty => nomatch empty)

abbrev zArena : Arena where
  signature := closedSignature
  Law readout := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (tag : State D),
    readout.readout () ⟨D, H⟩ tag = closedExpected D H tag

abbrev wArena : Arena where
  signature := closedSignature
  Law readout := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (tag : State D),
    readout.readout () ⟨D, H⟩ tag = closedExpected D H tag

def zSourceStatement : Prop :=
  ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ),
    Q D H (zState D) = 0

def wSourceStatement : Prop :=
  ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ),
    Q D H (wState D) = 0

theorem zSourceBridge : zSourceStatement ↔ zArena.Law zActual := by
  constructor
  · intro source D H tag
    simpa [zActual, closedExpected, realize, source D H, add_assoc]
  · intro law D H
    simpa [zActual, closedExpected, realize] using law D H 0

theorem wSourceBridge : wSourceStatement ↔ wArena.Law wActual := by
  constructor
  · intro source D H tag
    simpa [wActual, closedExpected, realize, source D H, add_assoc]
  · intro law D H
    simpa [wActual, closedExpected, realize] using law D H 0

theorem zActualPositive : zArena.Law zActual :=
  zSourceBridge.mp Q_z

theorem wActualPositive : wArena.Law wActual :=
  wSourceBridge.mp Q_w

theorem zRejected : ¬ zArena.Law closedReplacement := by
  intro law
  have equation := law probeLattice 0 (0 : State probeLattice)
  change closedExpected probeLattice 0 0 + vacuumState probeLattice =
    closedExpected probeLattice 0 0 at equation
  have zero : vacuumState probeLattice = 0 := by
    calc
      vacuumState probeLattice =
          (closedExpected probeLattice 0 0 + vacuumState probeLattice) -
            closedExpected probeLattice 0 0 := by module
      _ = closedExpected probeLattice 0 0 -
            closedExpected probeLattice 0 0 := by
        rw [equation]
      _ = 0 := by module
  have detected := congrArg
    (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.epsilon probeLattice) zero
  simpa [vacuumState, epsilon_vacuum] using detected

theorem wRejected : ¬ wArena.Law closedReplacement := by
  intro law
  have equation := law probeLattice 0 (0 : State probeLattice)
  change closedExpected probeLattice 0 0 + vacuumState probeLattice =
    closedExpected probeLattice 0 0 at equation
  have zero : vacuumState probeLattice = 0 := by
    calc
      vacuumState probeLattice =
          (closedExpected probeLattice 0 0 + vacuumState probeLattice) -
            closedExpected probeLattice 0 0 := by module
      _ = closedExpected probeLattice 0 0 -
            closedExpected probeLattice 0 0 := by
        rw [equation]
      _ = 0 := by module
  have detected := congrArg
    (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.epsilon probeLattice) zero
  simpa [vacuumState, epsilon_vacuum] using detected

theorem zDependence : ObservationalDependence closedSignature zActual := by
  intro role
  refine ⟨⟨probeLattice, 0⟩, (0 : State probeLattice),
    (vacuumState probeLattice), ?_⟩
  intro equality
  have detected := congrArg
    (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.epsilon probeLattice) equality
  simp [zActual, realize, vacuumState, epsilon_Q, epsilon_vacuum] at detected

theorem wDependence : ObservationalDependence closedSignature wActual := by
  intro role
  refine ⟨⟨probeLattice, 0⟩, (0 : State probeLattice),
    (vacuumState probeLattice), ?_⟩
  intro equality
  have detected := congrArg
    (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumClass.epsilon probeLattice) equality
  simp [wActual, realize, vacuumState, epsilon_Q, epsilon_vacuum] at detected

def zSource : Registration zArena zSourceStatement where
  actual := zActual
  bridge := zSourceBridge
  variation := ⟨zActualPositive, closedReplacement, zRejected⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      refine ⟨closedReplacement, ?_, rfl, zRejected⟩
      rintro ⟨⟩ distinct
      exact (distinct rfl).elim
    · intro empty
      exact Empty.elim empty
  dependence := zDependence

def wSource : Registration wArena wSourceStatement where
  actual := wActual
  bridge := wSourceBridge
  variation := ⟨wActualPositive, closedReplacement, wRejected⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      refine ⟨closedReplacement, ?_, rfl, wRejected⟩
      rintro ⟨⟩ distinct
      exact (distinct rfl).elim
    · intro empty
      exact Empty.elim empty
  dependence := wDependence

def zRegistration : Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix.Q_z)
    (Realization closedSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix.zUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix.zSource
  realizationSource := none
  generated := false
  arena := .source ⟨zArena⟩
  objectArena := .source ⟨zArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zArena ⟨zSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize closedSignature zActual.readout zActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def wRegistration : Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix.Q_w)
    (Realization closedSignature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix.wUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix.wSource
  realizationSource := none
  generated := false
  arena := .source ⟨wArena⟩
  objectArena := .source ⟨wArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source wArena ⟨wSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize closedSignature wActual.readout wActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms sourceBridge
#print axioms actualPositive
#print axioms rejected
#print axioms dependence
#print axioms source
#print axioms registration
#print axioms zSourceBridge
#print axioms wSourceBridge
#print axioms zActualPositive
#print axioms wActualPositive
#print axioms zRejected
#print axioms wRejected
#print axioms zDependence
#print axioms wDependence
#print axioms zSource
#print axioms wSource
#print axioms zRegistration
#print axioms wRegistration

end

end Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstNeutralMatrix
