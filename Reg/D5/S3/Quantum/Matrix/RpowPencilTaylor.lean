import D5.S3.Quantum.Matrix.RpowPencilTaylor
import Mathlib.Analysis.Calculus.Deriv.Abs
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound registration attempts for actual CFC cube-root calculus.
Source-selection binding remains unfinished for all six theorem registrations;
see https://github.com/the-omega-institute/trureturing/issues/23103.
Binding acceptance is separate from the mathematical kernel proofs. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix.RpowPencilTaylor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology ContDiff

namespace Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor
noncomputable section
universe u

private structure MatrixScope where
  index : Type u
  finiteIndex : Fintype index
  decidableIndex : DecidableEq index
attribute [instance] MatrixScope.finiteIndex MatrixScope.decidableIndex

private abbrev entrySignature : Signature where
  Params := Unit
  State _ := ℂ × ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def entryActual : Realization entrySignature :=
  realize entrySignature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)
private def entryRejected : Realization entrySignature :=
  realize entrySignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem entryDependence : ObservationalDependence entrySignature entryActual := by
  intro i
  exact ⟨(), (0,0), (0,1), by simp [entryActual, realize]⟩

private abbrev smoothSignature : Signature where
  Params := MatrixScope.{u}
  State s := ℝ → Matrix s.index s.index ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def smoothActual : Realization smoothSignature :=
  realize smoothSignature (fun _ _ f => ContDiffAt ℝ ∞ f 0) (fun e => nomatch e)
private def smoothRejected : Realization smoothSignature :=
  realize smoothSignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem smoothDependence : ObservationalDependence smoothSignature.{u} smoothActual := by
  intro i
  let p : MatrixScope.{u} := ⟨ULift.{u} Unit, inferInstance, inferInstance⟩
  let f : ℝ → Matrix p.index p.index ℂ := fun t => |t| • 1
  let L : Matrix p.index p.index ℂ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun A => (A ⟨()⟩ ⟨()⟩).re
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  refine ⟨p, (fun _ => 0), f, ?_⟩
  intro h
  change (ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : Matrix p.index p.index ℂ)) 0) =
    (ContDiffAt ℝ ∞ f 0) at h
  have hf : ContDiffAt ℝ ∞ f 0 := Eq.mp h contDiffAt_const
  have hh := L.contDiff.contDiffAt.comp 0 hf
  have hLf (t : ℝ) : L (f t) = |t| := by
    change ((|t| • (1 : Matrix p.index p.index ℂ)) ⟨()⟩ ⟨()⟩).re = |t|
    simp
  have ha : ContDiffAt ℝ ∞ (abs : ℝ → ℝ) 0 := by
    simpa only [Function.comp_def, hLf] using hh
  exact not_differentiableAt_abs_zero (ha.differentiableAt (by simp))

namespace CubicEntry
private abbrev arena : Arena where
  signature := entrySignature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {P : Matrix n n ℂ}
    (hP : P.IsHermitian) (E : Matrix n n ℂ) (i j : n),
    R.readout () () (spectralCoordinates hP (cubicLinear P E) i j,
      ((hP.eigenvalues i ^ 2 + hP.eigenvalues i * hP.eigenvalues j +
        hP.eigenvalues j ^ 2 : ℝ) : ℂ) * spectralCoordinates hP E i j)
private theorem rejected_law : ¬ arena.{u}.Law entryRejected := by
  intro h
  exact h (n := ULift.{u} Unit) (P := 0) (by simp : (0 : Matrix _ _ ℂ).IsHermitian)
    0 ⟨()⟩ ⟨()⟩
private theorem sensitivity : Sensitivity arena.{u} entryActual := by
  constructor
  · intro i
    refine ⟨entryRejected, ?_, ?_, rejected_law.{u}⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.cubicLinear_entry.{u})) where
  actual := entryActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.cubicLinear_entry.{u},
    entryRejected, rejected_law.{u}⟩
  sensitivity := sensitivity.{u}
  dependence := entryDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.cubicLinear_entry.{u})
    (Realization entrySignature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor.CubicEntry.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor.CubicEntry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize entrySignature (fun _ _ s => s.1 = s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end CubicEntry

namespace CubeRootSmooth
private abbrev arena : Arena where
  signature := smoothSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {Y K : Matrix n n ℂ}
    (hY : Y.PosDef) (hK : K.IsHermitian),
    R.readout () ⟨n, inferInstance, inferInstance⟩
      (fun t : ℝ => CFC.rpow (Y+t • K) (1/3 : ℝ))
private theorem rejected_law : ¬ arena.{u}.Law smoothRejected.{u} := by
  intro h
  exact h (n := ULift.{u} Unit) (Y := 1) (K := 0) Matrix.PosDef.one
    (by simp : (0 : Matrix _ _ ℂ).IsHermitian)
private theorem sensitivity : Sensitivity arena.{u} smoothActual.{u} := by
  constructor
  · intro i
    refine ⟨smoothRejected.{u}, ?_, ?_, rejected_law.{u}⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.contDiffAt_cubeRoot.{u})) where
  actual := smoothActual.{u}
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.contDiffAt_cubeRoot.{u},
    smoothRejected.{u}, rejected_law.{u}⟩
  sensitivity := sensitivity.{u}
  dependence := smoothDependence.{u}

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.contDiffAt_cubeRoot.{u})
    (Realization smoothSignature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor.CubeRootSmooth.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor.CubeRootSmooth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize smoothSignature.{u} (fun _ _ f => ContDiffAt ℝ ∞ f 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end CubeRootSmooth

private abbrev matrixEqSignature : Signature where
  Params := MatrixScope.{u}
  State s := Matrix s.index s.index ℂ × Matrix s.index s.index ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def matrixEqActual : Realization matrixEqSignature :=
  realize matrixEqSignature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)
private def matrixEqRejected : Realization matrixEqSignature :=
  realize matrixEqSignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem matrixEqDependence :
    ObservationalDependence matrixEqSignature.{u} matrixEqActual := by
  intro i
  let p : MatrixScope.{u} := ⟨ULift.{u} Unit, inferInstance, inferInstance⟩
  refine ⟨p, (0,0), (0,1), ?_⟩
  simp [matrixEqActual, realize, Matrix.ext_iff]

private abbrev recSignature : Signature where
  Params := MatrixScope.{u}
  State s := (Matrix s.index s.index ℂ × Matrix s.index s.index ℂ) ×
    (Matrix s.index s.index ℂ × Matrix s.index s.index ℂ) ×
    (Matrix s.index s.index ℂ × Matrix s.index s.index ℂ) ×
    (Matrix s.index s.index ℂ × Matrix s.index s.index ℂ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def recActual : Realization recSignature :=
  realize recSignature (fun _ _ s => s.1.1 = s.1.2 ∧ s.2.1.1 = s.2.1.2 ∧
    s.2.2.1.1 = s.2.2.1.2 ∧ s.2.2.2.1 = s.2.2.2.2) (fun e => nomatch e)
private def recRejected : Realization recSignature :=
  realize recSignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem recDependence : ObservationalDependence recSignature.{u} recActual := by
  intro i
  let p : MatrixScope.{u} := ⟨ULift.{u} Unit, inferInstance, inferInstance⟩
  refine ⟨p, ((0,0),(0,0),(0,0),(0,0)), ((0,1),(0,0),(0,0),(0,0)), ?_⟩
  simp [recActual, realize, Matrix.ext_iff]

private abbrev spectralSignature : Signature where
  Params := MatrixScope.{u}
  State s := (Matrix s.index s.index ℂ × Matrix s.index s.index ℂ) ×
    (s.index → s.index → ℝ) ×
    (Matrix s.index s.index ℂ × Matrix s.index s.index ℂ) ×
    (Matrix s.index s.index ℂ × Matrix s.index s.index ℂ) ×
    (Matrix s.index s.index ℂ × Matrix s.index s.index ℂ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def spectralActual : Realization spectralSignature :=
  realize spectralSignature (fun _ _ s => s.1.1 = s.1.2 ∧ ∀ i j,
    0 < s.2.1 i j ∧ s.2.2.1.1 i j = s.2.2.1.2 i j ∧
    s.2.2.2.1.1 i j = s.2.2.2.1.2 i j ∧ s.2.2.2.2.1 i j = s.2.2.2.2.2 i j)
    (fun e => nomatch e)
private def spectralRejected : Realization spectralSignature :=
  realize spectralSignature (fun _ _ _ => False) (fun e => nomatch e)
private theorem spectralDependence :
    ObservationalDependence spectralSignature.{u} spectralActual := by
  intro i
  let p : MatrixScope.{u} := ⟨ULift.{u} Unit, inferInstance, inferInstance⟩
  refine ⟨p, ((0,0),(fun _ _ => 1),(0,0),(0,0),(0,0)),
    ((0,0),(fun _ _ => 0),(0,0),(0,0),(0,0)), ?_⟩
  simp [spectralActual, realize]

namespace TwoThirdsSmooth
private abbrev arena : Arena where
  signature := smoothSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {Y K : Matrix n n ℂ}
    (hY : Y.PosDef) (hK : K.IsHermitian),
    R.readout () ⟨n, inferInstance, inferInstance⟩
      (fun t : ℝ => CFC.rpow (Y+t • K) (2/3 : ℝ))
private theorem rejected_law : ¬ arena.{u}.Law smoothRejected.{u} := by
  intro h
  exact h (n := ULift.{u} Unit) (Y := 1) (K := 0) Matrix.PosDef.one
    (by simp : (0 : Matrix _ _ ℂ).IsHermitian)
private theorem sensitivity : Sensitivity arena.{u} smoothActual.{u} := by
  constructor
  · intro i
    refine ⟨smoothRejected.{u}, ?_, ?_, rejected_law.{u}⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.contDiffAt_twoThirds.{u})) where
  actual := smoothActual.{u}
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.contDiffAt_twoThirds.{u},
    smoothRejected.{u}, rejected_law.{u}⟩
  sensitivity := sensitivity.{u}
  dependence := smoothDependence.{u}

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.contDiffAt_twoThirds.{u})
    (Realization smoothSignature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor.TwoThirdsSmooth.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor.TwoThirdsSmooth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize smoothSignature.{u} (fun _ _ f => ContDiffAt ℝ ∞ f 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end TwoThirdsSmooth

namespace RootRecurrences
private abbrev arena : Arena where
  signature := recSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {Y K : Matrix n n ℂ}
    (hY : Y.PosDef) (hK : K.IsHermitian),
    let P := CFC.rpow Y (1/3 : ℝ)
    let C := jetCoeff (fun t : ℝ => CFC.rpow (Y+t • K) (1/3 : ℝ))
    R.readout () ⟨n, inferInstance, inferInstance⟩
      ((C 0,P), (cubicLinear P (C 1),K),
        (cubicLinear P (C 2),-(P*C 1*C 1 + C 1*P*C 1 + C 1*C 1*P)),
        (cubicLinear P (C 3),-(P*C 1*C 2 + P*C 2*C 1 + C 1*P*C 2 + C 2*P*C 1 +
          C 1*C 2*P + C 2*C 1*P + C 1*C 1*C 1)))
private theorem rejected_law : ¬ arena.{u}.Law recRejected.{u} := by
  intro h
  exact h (n := ULift.{u} Unit) (Y := 1) (K := 0) Matrix.PosDef.one
    (by simp : (0 : Matrix _ _ ℂ).IsHermitian)
private theorem sensitivity : Sensitivity arena.{u} recActual.{u} := by
  constructor
  · intro i
    refine ⟨recRejected.{u}, ?_, ?_, rejected_law.{u}⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.cubeRoot_jet_recurrences.{u})) where
  actual := recActual.{u}
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.cubeRoot_jet_recurrences.{u},
    recRejected.{u}, rejected_law.{u}⟩
  sensitivity := sensitivity.{u}
  dependence := recDependence.{u}

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.cubeRoot_jet_recurrences.{u})
    (Realization recSignature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor.RootRecurrences.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor.RootRecurrences.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize recSignature.{u} (fun _ _ s => s.1.1 = s.1.2 ∧ s.2.1.1 = s.2.1.2 ∧
    s.2.2.1.1 = s.2.2.1.2 ∧ s.2.2.2.1 = s.2.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end RootRecurrences

namespace NormalizedJet
private abbrev arena : Arena where
  signature := matrixEqSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {Y K : Matrix n n ℂ}
    (hY : Y.PosDef) (hK : K.IsHermitian) (j : ℕ) (hj : j ≤ 3),
    let P := CFC.rpow Y (1/3 : ℝ)
    let C := jetCoeff (fun t : ℝ => CFC.rpow (Y+t • K) (1/3 : ℝ))
    R.readout () ⟨n, inferInstance, inferInstance⟩
      (jetCoeff (fun t : ℝ => P⁻¹ * CFC.rpow (Y+t • K) (2/3 : ℝ) * P⁻¹) j,
        P⁻¹ * (∑ a ∈ Finset.range (j+1), C a*C (j-a)) * P⁻¹)
private theorem rejected_law : ¬ arena.{u}.Law matrixEqRejected.{u} := by
  intro h
  exact h (n := ULift.{u} Unit) (Y := 1) (K := 0) Matrix.PosDef.one
    (by simp : (0 : Matrix _ _ ℂ).IsHermitian) 0 (by omega)
private theorem sensitivity : Sensitivity arena.{u} matrixEqActual.{u} := by
  constructor
  · intro i
    refine ⟨matrixEqRejected.{u}, ?_, ?_, rejected_law.{u}⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.normalized_twoThirds_jet.{u})) where
  actual := matrixEqActual.{u}
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.normalized_twoThirds_jet.{u},
    matrixEqRejected.{u}, rejected_law.{u}⟩
  sensitivity := sensitivity.{u}
  dependence := matrixEqDependence.{u}

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.normalized_twoThirds_jet.{u})
    (Realization matrixEqSignature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor.NormalizedJet.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor.NormalizedJet.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixEqSignature.{u} (fun _ _ s => s.1 = s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end NormalizedJet

namespace SpectralRecurrences
private abbrev arena : Arena where
  signature := spectralSignature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {Y K : Matrix n n ℂ}
    (hY : Y.PosDef) (hK : K.IsHermitian),
    let p := fun i => hY.isHermitian.eigenvalues i ^ (1/3 : ℝ)
    let T := Matrix.diagonal (fun i => (p i : ℂ))
    let e := spectralCoordinates hY.isHermitian
    let C := jetCoeff (fun t : ℝ => CFC.rpow (Y+t • K) (1/3 : ℝ))
    let D := fun a => e (C a)
    let d := fun i j => p i ^ 2 + p i*p j + p j ^ 2
    R.readout () ⟨n, inferInstance, inferInstance⟩
      ((D 0,T),d, ((fun i j => (d i j : ℂ)*D 1 i j), e K),
        ((fun i j => (d i j : ℂ)*D 2 i j), -(T*D 1*D 1 + D 1*T*D 1 + D 1*D 1*T)),
        ((fun i j => (d i j : ℂ)*D 3 i j), -(T*D 1*D 2 + T*D 2*D 1 + D 1*T*D 2 +
          D 2*T*D 1 + D 1*D 2*T + D 2*D 1*T + D 1*D 1*D 1)))
private theorem rejected_law : ¬ arena.{u}.Law spectralRejected.{u} := by
  intro h
  exact h (n := ULift.{u} Unit) (Y := 1) (K := 0) Matrix.PosDef.one
    (by simp : (0 : Matrix _ _ ℂ).IsHermitian)
private theorem sensitivity : Sensitivity arena.{u} spectralActual.{u} := by
  constructor
  · intro i
    refine ⟨spectralRejected.{u}, ?_, ?_, rejected_law.{u}⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.cubeRoot_jet_spectral.{u})) where
  actual := spectralActual.{u}
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.cubeRoot_jet_spectral.{u},
    spectralRejected.{u}, rejected_law.{u}⟩
  sensitivity := sensitivity.{u}
  dependence := spectralDependence.{u}

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.RpowPencilTaylor.cubeRoot_jet_spectral.{u})
    (Realization spectralSignature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor.SpectralRecurrences.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor.SpectralRecurrences.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize spectralSignature.{u} (fun _ _ s => s.1.1 = s.1.2 ∧ ∀ i j,
    0 < s.2.1 i j ∧ s.2.2.1.1 i j = s.2.2.1.2 i j ∧
    s.2.2.2.1.1 i j = s.2.2.2.1.2 i j ∧ s.2.2.2.2.1 i j = s.2.2.2.2.2 i j)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end SpectralRecurrences

end
end Reg.D5.S3.Quantum.Matrix.RpowPencilTaylor
