import D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound scalar observations retain each original telescope.
The source-selection reconstruction and escape coordinate are unfinished. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients
open _root_.D5.S3.Quantum.Matrix.PsdThreeCubic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder

namespace Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients
noncomputable section

private abbrev signature : Signature where
  Params := Unit
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

namespace H_pos
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 < s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q : ℝ) (hp : 0 < p) (hq : 0 < q), F.readout () () (0, H p q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 1), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.H_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.H_pos, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.H_pos) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.H_pos.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.H_pos.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 < s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end H_pos

namespace Q_pos
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 < s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r), F.readout () () (0, Q p q r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 1 (by norm_num) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 1), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Q_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Q_pos, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Q_pos) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Q_pos.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Q_pos.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 < s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Q_pos

namespace rho_closed
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q : ℝ) (hp : 0 < p) (hq : 0 < q), F.readout () () (rho p q, edgeNumerator p q/(12*(H p q)^4))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_closed)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_closed, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_closed) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_closed.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_closed.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end rho_closed

namespace rho_nonneg
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q : ℝ) (hp : 0 < p) (hq : 0 < q), F.readout () () (0, rho p q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_nonneg, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_nonneg) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_nonneg.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_nonneg.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end rho_nonneg

namespace rho_pos
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 < s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hne : p ≠ q), F.readout () () (0, rho p q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 2 (by norm_num) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 1), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_pos, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_pos) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_pos.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_pos.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 < s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end rho_pos

namespace rho_symm
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q : ℝ) (hp : 0 < p) (hq : 0 < q), F.readout () () (rho p q, rho q p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_symm)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_symm, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_symm) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_symm.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_symm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end rho_symm

namespace rho_self
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p : ℝ) (hp : 0 < p), F.readout () () (rho p p, 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_self)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_self, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_self) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_self.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.rho_self.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end rho_self

namespace F_swap_last
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q r : ℝ), F.readout () () (F p q r, F p r q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.F_swap_last)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.F_swap_last, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.F_swap_last) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.F_swap_last.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.F_swap_last.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end F_swap_last

namespace F_nonneg
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r), F.readout () () (0, F p q r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 1 (by norm_num) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.F_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.F_nonneg, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.F_nonneg) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.F_nonneg.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.F_nonneg.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end F_nonneg

namespace Xi_nonneg
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r), F.readout () () (0, Xi p q r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 1 (by norm_num) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_nonneg, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_nonneg) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_nonneg.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_nonneg.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Xi_nonneg

namespace Xi_double
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q : ℝ) (hp : 0 < p) (hq : 0 < q), F.readout () () (Xi p p q, 2*rho p q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_double)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_double, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_double) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_double.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_double.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Xi_double

namespace Xi_self
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p : ℝ), F.readout () () (Xi p p p, 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_self)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_self, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_self) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_self.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.Xi_self.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Xi_self

namespace edge_scaled
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r), F.readout () () (edgeScaled p q r, commonDen p q r*rho p q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 1 (by norm_num) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.edge_scaled)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.edge_scaled, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.edge_scaled) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.edge_scaled.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.edge_scaled.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end edge_scaled

namespace cycle_scaled
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r), F.readout () () (cycleScaled p q r, commonDen p q r*Xi p q r)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 1 (by norm_num) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.cycle_scaled)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.cycle_scaled, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.cycle_scaled) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.cycle_scaled.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.cycle_scaled.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end cycle_scaled

namespace p396_scaled
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r), F.readout () () (p396 p q r, (commonDen p q r)^3 * (4*(rho p q+rho q r+rho r p)*(rho p q*rho q r+rho q r*rho r p+rho r p*rho p q)+ 396*rho p q*rho q r*rho r p-(rho p q+rho q r+rho r p)*(Xi p q r)^2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 1 (by norm_num) (by norm_num) (by norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  norm_num [actual, realize]

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_scaled)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_scaled, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_scaled) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_scaled.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.p396_scaled.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1 = s.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end p396_scaled

end
end Reg.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients
