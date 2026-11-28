import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D
open _root_.D5.S3.Quantum.Gauge.CKMFlavorJarlskog4D
  (ckmStandard ckmStandard_unitary jarlskogQuartet jarlskog_bound_attained)
open LeanInformationAudit Matrix
open scoped Matrix

namespace Reg.D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D

set_option autoImplicit false

noncomputable section

abbrev seesawTraceSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def seesawTraceActual : Realization seesawTraceSignature :=
  realize seesawTraceSignature (fun _ mD M => (seesawMatrix mD M).trace) (fun e => nomatch e)

def seesawTraceErased : Realization seesawTraceSignature :=
  realize seesawTraceSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev seesawTraceArena : Arena where
  signature := seesawTraceSignature
  Law R := ∀ mD M : ℝ, (seesawMatrix mD M).det = -mD ^ 2 ∧ R.readout () mD M = M

private theorem seesaw_trace_erased_fails : ¬ seesawTraceArena.Law seesawTraceErased := by
  intro h
  exact zero_ne_one (show (0 : ℝ) = 1 from (h 0 1).2)

def seesawTraceFamily : Registration seesawTraceArena (type_of% (@seesaw_det_trace)) where
  actual := seesawTraceActual
  bridge := Iff.rfl
  variation := ⟨seesaw_det_trace, seesawTraceErased, seesaw_trace_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    seesawTraceArena.Law seesawTraceActual seesawTraceErased seesaw_trace_erased_fails
  dependence := by
    intro _
    refine ⟨0, 0, 1, ?_⟩
    change (seesawMatrix 0 0).trace ≠ (seesawMatrix 0 1).trace
    rw [(seesaw_det_trace 0 0).2, (seesaw_det_trace 0 1).2]
    exact zero_ne_one

def seesawTraceRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@seesaw_det_trace) (Realization seesawTraceSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D.seesaw_det_trace.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D.seesawTraceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨seesawTraceArena⟩
  objectArena := .source ⟨seesawTraceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source seesawTraceArena ⟨seesawTraceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize seesawTraceSignature
    (fun _ mD M => (seesawMatrix mD M).trace) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private theorem identity_baseline_samples :
    oscProb (1 : Matrix (Fin 2) (Fin 2) ℂ) (fun _ => 0) 0 0 0 = 1 ∧
      oscProb (1 : Matrix (Fin 2) (Fin 2) ℂ) (fun _ => 0) 0 0 1 = 0 := by
  have hu : (1 : Matrix (Fin 2) (Fin 2) ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
    simp
  constructor
  · simpa using oscProb_zero_baseline (1 : Matrix (Fin 2) (Fin 2) ℂ) (fun _ => 0) 0 0 hu
  · simpa using oscProb_zero_baseline (1 : Matrix (Fin 2) (Fin 2) ℂ) (fun _ => 0) 0 1 hu

abbrev probabilitySignParams :=
  Σ n : ℕ, Σ _ : Matrix (Fin n) (Fin n) ℂ, Σ _ : Fin n → ℝ, Σ _ : ℝ, Fin n

abbrev probabilitySignSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature probabilitySignParams
    (fun p => Fin p.1) (fun _ => ℝ)

def probabilitySignActual : Realization probabilitySignSignature :=
  realize probabilitySignSignature
    (fun _ p β => oscProb p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 β) (fun e => nomatch e)

def probabilitySignErased : Realization probabilitySignSignature :=
  realize probabilitySignSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev probabilitySignArena : Arena where
  signature := probabilitySignSignature
  Law R := ∀ {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (mSq : Fin n → ℝ) (x : ℝ)
    (α β : Fin n), 0 ≤ R.readout () ⟨n, U, mSq, x, α⟩ β

private theorem probability_sign_erased_fails : ¬ probabilitySignArena.Law probabilitySignErased := by
  intro h
  have hbad := h (n := 2) 1 (fun _ => 0) 0 0 0
  change (0 : ℝ) ≤ -1 at hbad
  norm_num at hbad

def probabilitySignFamily : Registration probabilitySignArena (type_of% (@oscProb_nonneg)) where
  actual := probabilitySignActual
  bridge := Iff.rfl
  variation := ⟨@oscProb_nonneg, probabilitySignErased, probability_sign_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    probabilitySignArena.Law probabilitySignActual probabilitySignErased probability_sign_erased_fails
  dependence := by
    intro _
    refine ⟨⟨2, 1, fun _ => 0, 0, 0⟩, 0, 1, ?_⟩
    change oscProb (1 : Matrix (Fin 2) (Fin 2) ℂ) (fun _ => 0) 0 0 0 ≠
      oscProb (1 : Matrix (Fin 2) (Fin 2) ℂ) (fun _ => 0) 0 0 1
    rw [identity_baseline_samples.1, identity_baseline_samples.2]
    norm_num

def probabilitySignRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@oscProb_nonneg) (Realization probabilitySignSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D.oscProb_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D.probabilitySignFamily
  realizationSource := none
  generated := false
  arena := .source ⟨probabilitySignArena⟩
  objectArena := .source ⟨probabilitySignArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source probabilitySignArena ⟨probabilitySignFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize probabilitySignSignature
    (fun _ p β => oscProb p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 β) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev zeroBaselineParams := Σ n : ℕ, Σ _ : Matrix (Fin n) (Fin n) ℂ, Σ _ : Fin n → ℝ, Fin n

abbrev zeroBaselineSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature zeroBaselineParams
    (fun p => Fin p.1) (fun _ => ℝ)

def zeroBaselineActual : Realization zeroBaselineSignature :=
  realize zeroBaselineSignature
    (fun _ p β => oscProb p.2.1 p.2.2.1 0 p.2.2.2 β) (fun e => nomatch e)

def zeroBaselineErased : Realization zeroBaselineSignature :=
  realize zeroBaselineSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev zeroBaselineArena : Arena where
  signature := zeroBaselineSignature
  Law R := ∀ {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (mSq : Fin n → ℝ)
    (α β : Fin n), U * Uᴴ = 1 → R.readout () ⟨n, U, mSq, α⟩ β = if α = β then 1 else 0

private theorem zero_baseline_erased_fails : ¬ zeroBaselineArena.Law zeroBaselineErased := by
  intro h
  have hbad := h (n := 2) 1 (fun _ => 0) 0 0 (by simp)
  change (0 : ℝ) = (if (0 : Fin 2) = 0 then 1 else 0) at hbad
  norm_num at hbad

def zeroBaselineFamily : Registration zeroBaselineArena (type_of% (@oscProb_zero_baseline)) where
  actual := zeroBaselineActual
  bridge := Iff.rfl
  variation := ⟨@oscProb_zero_baseline, zeroBaselineErased, zero_baseline_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    zeroBaselineArena.Law zeroBaselineActual zeroBaselineErased zero_baseline_erased_fails
  dependence := by
    intro _
    refine ⟨⟨2, 1, fun _ => 0, 0⟩, 0, 1, ?_⟩
    change oscProb (1 : Matrix (Fin 2) (Fin 2) ℂ) (fun _ => 0) 0 0 0 ≠
      oscProb (1 : Matrix (Fin 2) (Fin 2) ℂ) (fun _ => 0) 0 0 1
    rw [identity_baseline_samples.1, identity_baseline_samples.2]
    norm_num

def zeroBaselineRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@oscProb_zero_baseline) (Realization zeroBaselineSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D.oscProb_zero_baseline.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D.zeroBaselineFamily
  realizationSource := none
  generated := false
  arena := .source ⟨zeroBaselineArena⟩
  objectArena := .source ⟨zeroBaselineArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zeroBaselineArena ⟨zeroBaselineFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize zeroBaselineSignature
    (fun _ p β => oscProb p.2.1 p.2.2.1 0 p.2.2.2 β) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


private def cpWitnessMixing : Matrix (Fin 3) (Fin 3) ℂ :=
  ckmStandard (Real.pi / 4) (Real.pi / 4) (Real.arcsin (1 / Real.sqrt 3)) (Real.pi / 2)

private def cpWitnessMassSq : Fin 3 → ℝ := ![0, Real.pi / 2, Real.pi]

private theorem cp_witness_unitary : cpWitnessMixingᴴ * cpWitnessMixing = 1 :=
  (ckmStandard_unitary _ _ _ _).1

private theorem cp_witness_formula :
    cpAsymmetry cpWitnessMixing cpWitnessMassSq 1 0 1 =
      16 * (1 / (6 * Real.sqrt 3)) * Real.sin (Real.pi / 4) *
        Real.sin (Real.pi / 4) * Real.sin (Real.pi / 2) := by
  rw [three_flavor_cp_asymmetry_jarlskog _ cp_witness_unitary]
  change 16 * jarlskogQuartet cpWitnessMixing 0 0 1 1 *
    Real.sin (((Real.pi / 2 - 0) * 1) / 2) *
    Real.sin (((Real.pi - Real.pi / 2) * 1) / 2) *
    Real.sin (((Real.pi - 0) * 1) / 2) = _
  rw [show jarlskogQuartet cpWitnessMixing 0 0 1 1 = 1 / (6 * Real.sqrt 3) from
    jarlskog_bound_attained.2]
  rw [show ((Real.pi / 2 - 0) * 1) / 2 = Real.pi / 4 by ring,
    show ((Real.pi - Real.pi / 2) * 1) / 2 = Real.pi / 4 by ring,
    show ((Real.pi - 0) * 1) / 2 = Real.pi / 2 by ring]

private theorem cp_witness_ne_zero : cpAsymmetry cpWitnessMixing cpWitnessMassSq 1 0 1 ≠ 0 := by
  rw [cp_witness_formula, Real.sin_pi_div_four, Real.sin_pi_div_two]
  positivity

abbrev asymmetryParams :=
  Σ _ : Matrix (Fin 3) (Fin 3) ℂ, Σ _ : Fin 3 → ℝ, Σ _ : ℝ, Fin 3

abbrev asymmetrySignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature asymmetryParams
    (fun _ => Fin 3) (fun _ => ℝ)

def asymmetryActual : Realization asymmetrySignature :=
  realize asymmetrySignature
    (fun _ p β => cpAsymmetry p.1 p.2.1 p.2.2.1 p.2.2.2 β) (fun e => nomatch e)

def asymmetryErased : Realization asymmetrySignature :=
  realize asymmetrySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev asymmetryArena : Arena where
  signature := asymmetrySignature
  Law R := ∀ (U : Matrix (Fin 3) (Fin 3) ℂ), Uᴴ * U = 1 →
    ∀ (mSq : Fin 3 → ℝ) (x : ℝ) (α β : Fin 3),
    let Δ21 := mSq 1 - mSq 0
    let Δ32 := mSq 2 - mSq 1
    let Δ31 := mSq 2 - mSq 0
    R.readout () ⟨U, mSq, x, α⟩ β =
      16 * jarlskogQuartet U α 0 β 1 * Real.sin (Δ21 * x / 2) *
        Real.sin (Δ32 * x / 2) * Real.sin (Δ31 * x / 2)

private theorem asymmetry_erased_fails : ¬ asymmetryArena.Law asymmetryErased := by
  intro h
  apply cp_witness_ne_zero
  have he := h cpWitnessMixing cp_witness_unitary cpWitnessMassSq 1 0 1
  rw [three_flavor_cp_asymmetry_jarlskog _ cp_witness_unitary]
  exact he.symm

def asymmetryFamily : Registration asymmetryArena
    (type_of% (@three_flavor_cp_asymmetry_jarlskog)) where
  actual := asymmetryActual
  bridge := Iff.rfl
  variation := ⟨@three_flavor_cp_asymmetry_jarlskog, asymmetryErased, asymmetry_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    asymmetryArena.Law asymmetryActual asymmetryErased asymmetry_erased_fails
  dependence := by
    intro _
    refine ⟨⟨cpWitnessMixing, cpWitnessMassSq, 1, 0⟩, 1, 0, ?_⟩
    change cpAsymmetry cpWitnessMixing cpWitnessMassSq 1 0 1 ≠
      cpAsymmetry cpWitnessMixing cpWitnessMassSq 1 0 0
    rw [(cpAsymmetry_antisymm cpWitnessMixing cpWitnessMassSq 1 0 1).2]
    exact cp_witness_ne_zero

def asymmetryRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@three_flavor_cp_asymmetry_jarlskog) (Realization asymmetrySignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D.three_flavor_cp_asymmetry_jarlskog.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D.asymmetryFamily
  realizationSource := none
  generated := false
  arena := .source ⟨asymmetryArena⟩
  objectArena := .source ⟨asymmetryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source asymmetryArena ⟨asymmetryFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize asymmetrySignature
    (fun _ p β => cpAsymmetry p.1 p.2.1 p.2.2.1 p.2.2.2 β) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Gauge.SeesawNeutrinoOscillations4D
