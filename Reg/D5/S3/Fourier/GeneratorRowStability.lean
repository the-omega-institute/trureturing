import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.GeneratorRowStability
import Reg.Support.DependentFamily
import Mathlib.Tactic

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.GeneratorRowStability
open LeanInformationAudit Finset
open scoped BigOperators ComplexConjugate

noncomputable section
namespace Reg.D5.S3.Fourier.GeneratorRowStability

abbrev Parameters := Σ N : ℕ, ZMod N → ℂ

abbrev signature : Signature where
  Params := Parameters
  State p := ZMod p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => p.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Observation varies within one nonconstant order-two phase family. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  let z : ZMod 2 → ℂ := fun k => if k = 0 then 1 else -1
  refine ⟨⟨2, z⟩, 0, 1, ?_⟩
  norm_num [actual, realize, z]

namespace Phase

def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} [NeZero N] (z : ZMod N → ℂ)
    (θ : ZMod N → ℝ) (ω : ℝ),
    z 0 = 1 → (∀ k, ‖z k‖ = 1) → θ 0 = 0 →
    (∀ k, Complex.exp (↑(θ k) * Complex.I) =
      z k * z 1 * conj (z (k + 1))) →
    0 ≤ ω → (∀ k, |θ k| ≤ ω) →
    ∃ t : ZMod N, ∀ k,
      ‖R.readout () ⟨N, z⟩ k - ZMod.stdAddChar (-(k * t))‖ ≤
        (N - 1 : ℝ) * ω / 2

/-- Zero observation fails at the lawful order-one, zero-tolerance endpoint. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨t, ht⟩ := h (fun _ : ZMod 1 => 1) (fun _ => 0) 0
    rfl (by intro k; norm_num) rfl (by intro k; simp)
    (by norm_num) (by intro k; norm_num)
  have h0 := ht 0
  norm_num [rejected, realize] at h0

def registration : Registration arena (type_of% (@complete_cycle_phase_correction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@complete_cycle_phase_correction, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration_1 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@complete_cycle_phase_correction)
      (type_of% (realize signature (fun _ p x => p.2 x) (fun e => nomatch e)))
      Unit Unit := {
  unitName := `D5.S3.Fourier.GeneratorRowStability.complete_cycle_phase_correction.information_unit,
  realizationName := `Reg.D5.S3.Fourier.GeneratorRowStability.Phase.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p x => p.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.GeneratorRowStability,
    definition := none,
    coordinates := #[0, 2],
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "body",
        "fn", "arg", "arg", "fn", "arg"],
      stateBinder := 12,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
end Phase

namespace Signal

def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) (m ε : ℝ),
    0 < m → 0 ≤ ε → ε ≤ m ^ 3 / 4 →
    ZMod.dft f 0 = ZMod.dft g 0 →
    (∀ k, m ≤ ‖ZMod.dft f k‖) →
    (∀ k, ‖ZMod.dft g k‖ = ‖ZMod.dft f k‖) →
    (∀ k, ‖ZMod.dft g k * ZMod.dft g 1 * conj (ZMod.dft g (k + 1)) -
      ZMod.dft f k * ZMod.dft f 1 * conj (ZMod.dft f (k + 1))‖ ≤ ε) →
    ∃ t : ZMod N,
      ∑ x, ‖R.readout () ⟨N, g⟩ x - f (x - t)‖ ^ 2 ≤
        16 * (N - 1 : ℝ) ^ 2 * ε ^ 2 * sourceEnergy f / (63 * m ^ 6)

/-- Exact DC at order one makes every zero-output replacement fail. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let f : ZMod 1 → ℂ := fun _ => 1
  have hf (k : ZMod 1) : ZMod.dft f k = 1 := by
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rw [ZMod.dft_apply_zero]
    simp [f]
  obtain ⟨t, ht⟩ := h f f 1 0 (by norm_num) (by norm_num) (by norm_num)
    rfl (by intro k; rw [hf]; norm_num) (by intro k; rfl) (by intro k; simp)
  norm_num [rejected, realize, f, ZMod.card] at ht

/-- A positive nonconstant order-two signal varies within the observed family. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  let g : ZMod 2 → ℂ := fun x => if x = 0 then 2 else 1
  refine ⟨⟨2, g⟩, 0, 1, ?_⟩
  norm_num [actual, realize, g]

def registration : Registration arena
    (type_of% (@equal_amplitude_signal_energy_stability)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@equal_amplitude_signal_energy_stability, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration_1 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@equal_amplitude_signal_energy_stability)
      (type_of% (realize signature (fun _ p x => p.2 x) (fun e => nomatch e)))
      Unit Unit := {
  unitName :=
    `D5.S3.Fourier.GeneratorRowStability.equal_amplitude_signal_energy_stability.information_unit,
  realizationName := `Reg.D5.S3.Fourier.GeneratorRowStability.Signal.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p x => p.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.GeneratorRowStability,
    definition := none,
    coordinates := #[0, 3],
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg",
        "body", "fn", "arg", "arg", "body", "fn", "arg",
        "arg", "fn", "arg"],
      stateBinder := 14,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
end Signal
namespace UnequalSignal

def arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) (m ε : ℝ),
    0 < m → 0 ≤ ε → ε ≤ m ^ 3 / 4 →
    ZMod.dft f 0 = ZMod.dft g 0 →
    (∀ k, m ≤ ‖ZMod.dft f k‖) →
    (∀ k, ‖ZMod.dft g 0 * ZMod.dft g k * conj (ZMod.dft g k) -
      ZMod.dft f 0 * ZMod.dft f k * conj (ZMod.dft f k)‖ ≤ ε) →
    (∀ k, ‖ZMod.dft g k * ZMod.dft g 1 * conj (ZMod.dft g (k + 1)) -
      ZMod.dft f k * ZMod.dft f 1 * conj (ZMod.dft f (k + 1))‖ ≤ ε) →
    ∃ t : ZMod N,
      ∑ x, ‖R.readout () ⟨N, g⟩ x - f (x - t)‖ ^ 2 ≤
        ε ^ 2 * sourceEnergy f * (1 + (N - 1 : ℝ) ^ 2) / (3 * m ^ 6)

/-- Exact DC at order one makes every zero-output replacement fail. -/
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let f : ZMod 1 → ℂ := fun _ => 1
  have hf (k : ZMod 1) : ZMod.dft f k = 1 := by
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rw [ZMod.dft_apply_zero]
    simp [f]
  obtain ⟨t, ht⟩ := h f f 1 0 (by norm_num) (by norm_num) (by norm_num)
    rfl (by intro k; rw [hf]; norm_num) (by intro k; simp) (by intro k; simp)
  norm_num [rejected, realize, f, ZMod.card] at ht

/-- A positive nonconstant order-two signal varies within the observed family. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  let g : ZMod 2 → ℂ := fun x => if x = 0 then 2 else 1
  refine ⟨⟨2, g⟩, 0, 1, ?_⟩
  norm_num [actual, realize, g]

def registration : Registration arena
    (type_of% (@unequal_amplitude_signal_energy_stability)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@unequal_amplitude_signal_energy_stability, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration_1 :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@unequal_amplitude_signal_energy_stability)
      (type_of% (realize signature (fun _ p x => p.2 x) (fun e => nomatch e)))
      Unit Unit := {
  unitName :=
    `D5.S3.Fourier.GeneratorRowStability.unequal_amplitude_signal_energy_stability.information_unit,
  realizationName := `Reg.D5.S3.Fourier.GeneratorRowStability.UnequalSignal.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p x => p.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.GeneratorRowStability,
    definition := none,
    coordinates := #[0, 3],
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg",
        "body", "fn", "arg", "arg", "body", "fn", "arg",
        "arg", "fn", "arg"],
      stateBinder := 14,
      functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
end UnequalSignal
end Reg.D5.S3.Fourier.GeneratorRowStability
