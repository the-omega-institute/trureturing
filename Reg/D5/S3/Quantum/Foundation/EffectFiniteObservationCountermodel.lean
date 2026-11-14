import D5.S3.Quantum.Foundation.EffectFiniteObservationCountermodel
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
open scoped ComplexOrder MatrixOrder
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.EffectFiniteObservationCountermodel

namespace Reg.D5.S3.Quantum.Foundation.EffectFiniteObservationCountermodel

abbrev signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law O := ∀ (d : ℕ) (hd : 1 ≤ d)
      (T : Finset {E : Matrix (Fin d) (Fin d) ℂ // E.PosSemidef ∧ (1 - E).PosSemidef})
      (ρstar : Matrix (Fin d) (Fin d) ℂ)
      (hρstar : ρstar.PosSemidef) (htrstar : Matrix.trace ρstar = 1),
    ∃ p : Matrix (Fin d) (Fin d) ℂ → ℝ,
      Measurable p ∧
      (∀ E : Matrix (Fin d) (Fin d) ℂ,
        E.PosSemidef ∧ (1 - E).PosSemidef → 0 ≤ p E ∧ p E ≤ 1) ∧
      O.readout () d p = 0 ∧ p 1 = 1 ∧
      (∀ E ∈ T, p E.1 = (Matrix.trace (ρstar * E.1)).re) ∧
      (∀ E F : Matrix (Fin d) (Fin d) ℂ, E.PosSemidef → F.PosSemidef →
        (1 - (E + F)).PosSemidef → |p (E + F) - p E - p F| ≤ 2) ∧
      (∃ E F : Matrix (Fin d) (Fin d) ℂ,
        E ≠ F ∧ E.PosSemidef ∧ F.PosSemidef ∧
        (1 - (E + F)).PosSemidef ∧ |p (E + F) - p E - p F| = 2) ∧
      (∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
        (∀ E : Matrix (Fin d) (Fin d) ℂ,
          E.PosSemidef ∧ (1 - E).PosSemidef →
            |p E - (Matrix.trace (ρ * E)).re| ≤ 1) ∧
        ∀ η : ℝ, 0 < η → ∃ E : Matrix (Fin d) (Fin d) ℂ,
          (E.PosSemidef ∧ (1 - E).PosSemidef) ∧
            1 - η < |p E - (Matrix.trace (ρ * E)).re|)

abbrev source : Prop := type_of% (@finite_observation_countermodel)

theorem source_bridge : source ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual :=
  source_bridge.mp finite_observation_countermodel

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, hp⟩ := h 1 (by decide) ∅ 1 Matrix.PosSemidef.one (by simp)
  have contradiction : (1 : ℝ) = 0 := hp.2.2.1
  norm_num at contradiction

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  change (0 : ℝ) ≠ 1
  norm_num

def evidence : Registration arena source where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Foundation.EffectFiniteObservationCountermodel.finite_observation_countermodel)
    (type_of% (realize signature (fun _ _ p => p 0) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Quantum.Foundation.EffectFiniteObservationCountermodel.finite_observation_countermodel.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Foundation.EffectFiniteObservationCountermodel.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Foundation.EffectFiniteObservationCountermodel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration
end Reg.D5.S3.Quantum.Foundation.EffectFiniteObservationCountermodel
