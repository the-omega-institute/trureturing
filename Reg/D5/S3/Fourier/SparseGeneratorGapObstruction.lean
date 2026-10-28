import Batteries.Tactic.OpenPrivate
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.SparseGeneratorGapObstruction
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.SparseGeneratorGapObstruction
open LeanInformationAudit
open private lower_endpoint translation_dependence
  from D5.S3.Fourier.SparseGeneratorGapObstruction
open scoped BigOperators ComplexConjugate

noncomputable section
namespace Reg.D5.S3.Fourier.SparseGeneratorGapObstruction

abbrev signature : Signature where
  Params := ℕ
  State N := ZMod N
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ N t => countingError (sourceSignal N) (targetSignal N) t)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ) [NeZero N] (hN : familyDomain N),
    0 ∉ familySet N ∧
    (∀ s, s ∈ familySet N ↔ -s ∈ familySet N) ∧
    (familySet N).card = 2 * sampleSize N ∧
    (familySet N).Nonempty ∧ generating (familySet N) ∧
    1 ≤ ordinaryGap (familySet N) ∧
    (∀ k : ZMod N, ZMod.dft (sourceSignal N) k = 1) ∧
    ZMod.dft (targetSignal N) = phaseSpectrum N ∧
    (∀ k : ZMod N, ‖ZMod.dft (sourceSignal N) k‖ = 1 ∧
      ‖ZMod.dft (targetSignal N) k‖ = 1) ∧
    phaseSpectrum N 0 = 1 ∧ (∀ s ∈ familySet N, phaseSpectrum N s = 1) ∧
    ZMod.dft (sourceSignal N) 0 = 1 ∧ ZMod.dft (targetSignal N) 0 = 1 ∧
    (∀ k, bispectrum (ZMod.dft (targetSignal N)) k 0 =
      bispectrum (ZMod.dft (sourceSignal N)) k 0) ∧
    (∀ s ∈ familySet N, ∀ k,
      ‖bispectrum (ZMod.dft (targetSignal N)) k s -
        bispectrum (ZMod.dft (sourceSignal N)) k s‖ ≤ observationTolerance N) ∧
    0 < observationTolerance N ∧ observationTolerance N ≤ Real.pi / 16 ∧
    Real.pi / 16 < 1 / 4 ∧
    _root_.D5.S3.Fourier.GeneratorRowStability.sourceEnergy (sourceSignal N) = ((N : ℝ) - 1) / N ∧
    (∀ t : ZMod N, R.readout () N t ∈
      Set.Icc (2 - 2 * Real.sqrt 2 / Real.sqrt N) (2 + 2 * Real.sqrt 2 / Real.sqrt N)) ∧
    ∀ K : ℝ, (∃ t : ZMod N, countingError (sourceSignal N) (targetSignal N) t ≤
      K * observationTolerance N ^ 2 * _root_.D5.S3.Fourier.GeneratorRowStability.sourceEnergy (sourceSignal N) /
        ordinaryGap (familySet N)) → logOrder N ^ 2 / (256 * Real.pi ^ 2) ≤ K

private lemma actual_bridge : (type_of% (@parameter_family)) ↔ arena.Law actual :=
  Iff.rfl

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let N := Nat.ceil (Real.exp 128)
  have hN : familyDomain N := le_rfl
  haveI : NeZero N := ⟨Nat.ne_of_gt (large_order_pos hN)⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, herr, _⟩ := h N hN
  have hh := (herr 0).1
  have hlo := lower_endpoint hN
  change 2 - 2 * Real.sqrt 2 / Real.sqrt N ≤ 0 at hh
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let N := Nat.ceil (Real.exp 128)
  have hN : familyDomain N := le_rfl
  haveI : NeZero N := ⟨Nat.ne_of_gt (large_order_pos hN)⟩
  obtain ⟨t, ht⟩ := translation_dependence hN
  refine ⟨N, t, 0, ?_⟩
  exact ht

def registration : Registration arena (type_of% (@parameter_family)) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨actual_bridge.mp (@parameter_family), rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@parameter_family)
    (type_of% (realize signature
      (fun _ N t => countingError (sourceSignal N) (targetSignal N) t)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Fourier.SparseGeneratorGapObstruction.parameter_family.information_unit,
  realizationName := `Reg.D5.S3.Fourier.SparseGeneratorGapObstruction.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature
    (fun _ N t => countingError (sourceSignal N) (targetSignal N) t)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.SparseGeneratorGapObstruction,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #["body","body","body","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","fn","arg","body","arg"],
      stateBinder := 3,
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

end Reg.D5.S3.Fourier.SparseGeneratorGapObstruction
end
