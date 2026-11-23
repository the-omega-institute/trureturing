import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot
import Reg.Support.SingleDependentReadout

/-! Source-bound audits for the physical Petz qubit root. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot
open scoped ComplexOrder Matrix.Norms.Elementwise

namespace Reg.D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => Qubit)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

namespace BlockPosDef

private def actual : Realization signature :=
  realize signature (fun _ p c => unscaledBlock p.1 p.2 c) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x η c : ℝ}, 0 < η → 0 < 1 - x → 0 < detFactor x c →
    (R.readout () ⟨x, η⟩ c).PosDef

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : (0 : Qubit).PosDef :=
    h (x := 0) (η := 1) (c := 0) (by norm_num) (by norm_num) (by norm_num [detFactor])
  simpa using hp.det_pos

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1 / 2, 1⟩, 0, 1 / 2, fun h => ?_⟩
  have hentry := congrArg (fun A : Qubit => (A 0 1).re) h
  norm_num [actual, realize, unscaledBlock, qubit] at hentry

def sourceRegistration : Registration arena (type_of% @unscaledBlock_posDef) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@unscaledBlock_posDef, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@unscaledBlock_posDef) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot.unscaledBlock_posDef.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot.BlockPosDef.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p c => unscaledBlock p.1 p.2 c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BlockPosDef

private theorem root_dependence :
    ObservationalDependence signature
      (realize signature (fun _ p => normalizedRoot p.1 p.2) (fun e => nomatch e)) := by
  intro i
  by_contra! h
  have hconst : normalizedRoot (1 / 2) 1 = fun _ => normalizedRoot (1 / 2) 1 0 := by
    funext c
    exact h ⟨1 / 2, 1⟩ c 0
  have hd := (normalizedRoot_firstVariation (x := 1 / 2) (η := 1)
    (by norm_num) (by norm_num) (by norm_num)).2
  rw [hconst] at hd
  have hentry := congrArg (fun A : Qubit => (A 0 1).re) (hd.unique (hasDerivAt_const _ _))
  have hpos : 0 < 2 * (1 / 2 : ℝ) * 1 /
      (1 * Real.sqrt (1 - 1 / 2) + Real.sqrt (1 + 1 / 2)) := by positivity
  exact hpos.ne' hentry

namespace RootFormula

private def actual : Realization signature :=
  realize signature (fun _ p => normalizedRoot p.1 p.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x η c : ℝ}, 0 < η → 0 < 1 - x → 0 < 1 + x → 0 < detFactor x c →
    R.readout () ⟨x, η⟩ c =
      qubit ((η * (1 - x) + Real.sqrt (detFactor x c)) / rootDen x η c)
        (η * (2 * x * c) / rootDen x η c)
        (2 * x * c / rootDen x η c)
        (((1 + x) + η * Real.sqrt (detFactor x c)) / rootDen x η c)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hentry := congrArg (fun A : Qubit => (A 0 0).re)
    (h (x := 0) (η := 1) (c := 0) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [detFactor]))
  have hp : 0 < (1 * (1 - 0) + Real.sqrt (detFactor 0 0)) / rootDen 0 1 0 := by
    unfold rootDen
    positivity
  exact hp.ne' hentry.symm

def sourceRegistration : Registration arena (type_of% @normalizedRoot_formula) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalizedRoot_formula, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := root_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@normalizedRoot_formula) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot.normalizedRoot_formula.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot.RootFormula.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => normalizedRoot p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RootFormula

namespace RootVariation

private def actual : Realization signature :=
  realize signature (fun _ p => normalizedRoot p.1 p.2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x η : ℝ}, 0 < η → 0 < 1 - x → 0 < 1 + x →
    let denom := η * Real.sqrt (1 - x) + Real.sqrt (1 + x)
    R.readout () ⟨x, η⟩ 0 = qubit (Real.sqrt (1 - x)) 0 0 (Real.sqrt (1 + x)) ∧
      HasDerivAt (R.readout () ⟨x, η⟩)
        (qubit 0 (2 * x * η / denom) (2 * x / denom) 0) 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hentry := congrArg (fun A : Qubit => (A 0 0).re)
    (h (x := 0) (η := 1) (by norm_num) (by norm_num) (by norm_num)).1
  change (0 : ℝ) = Real.sqrt (1 - 0) at hentry
  norm_num at hentry

def sourceRegistration : Registration arena (type_of% @normalizedRoot_firstVariation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalizedRoot_firstVariation, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := root_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@normalizedRoot_firstVariation) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot.normalizedRoot_firstVariation.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot.RootVariation.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p => normalizedRoot p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RootVariation

end Reg.D5.S3.Quantum.Recovery.PetzPhysicalQubitRoot
