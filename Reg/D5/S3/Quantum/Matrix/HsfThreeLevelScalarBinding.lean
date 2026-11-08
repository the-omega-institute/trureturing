import D5.S3.Quantum.Matrix.HsfThreeLevelScalarBinding
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

namespace Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarBinding
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

namespace scalar_p396_margin
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r), F.readout () () ((rho p q+rho q r+rho r p)*(Xi p q r)^2, 4*(rho p q+rho q r+rho r p)*(rho p q*rho q r+rho q r*rho r p+rho r p*rho p q)+ 396*rho p q*rho q r*rho r p)

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

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.scalar_p396_margin)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.scalar_p396_margin, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.scalar_p396_margin) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarBinding.scalar_p396_margin.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarBinding.scalar_p396_margin.family
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
end scalar_p396_margin

namespace coefficient_domination
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r), F.readout () () (Xi p q r, allowance (rho p q) (rho q r) (rho r p))

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

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.coefficient_domination)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.coefficient_domination, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.coefficient_domination) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarBinding.coefficient_domination.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarBinding.coefficient_domination.family
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
end coefficient_domination

namespace closed_cubic_nonneg
private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1 ≤ s.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (S : Mat) (hS : S.PosSemidef), F.readout () () (0, closedCubic p q r S)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 1 1 (by norm_num) (by norm_num) (by norm_num) 0 Matrix.PosSemidef.zero

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

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.closed_cubic_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.closed_cubic_nonneg, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients.closed_cubic_nonneg) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarBinding.closed_cubic_nonneg.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarBinding.closed_cubic_nonneg.family
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
end closed_cubic_nonneg

end
end Reg.D5.S3.Quantum.Matrix.HsfThreeLevelScalarBinding
