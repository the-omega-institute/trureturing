import Batteries.Tactic.OpenPrivate
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.GeneratorRowOrderNecessity
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.GeneratorRowOrderNecessity
open LeanInformationAudit
open private bispectrum countingError observationTolerance
  from D5.S3.Fourier.GeneratorRowOrderNecessity

open scoped BigOperators ComplexConjugate

noncomputable section
namespace Reg.D5.S3.Fourier.GeneratorRowOrderNecessity

abbrev signature : Signature where
  Params := Parameter
  State p := ZMod (order p)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p t => countingError (sourceSignal p) (targetSignal p) t)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p : Parameter,
    ZMod.dft (sourceSignal p) = sourceSpectrum p ∧
    ZMod.dft (targetSignal p) = foldedSpectrum p ∧
    ZMod.dft (sourceSignal p) 0 = (1 : ℂ) ∧
    ZMod.dft (targetSignal p) 0 = (1 : ℂ) ∧
    (∀ k, ‖ZMod.dft (sourceSignal p) k‖ = 1 ∧
      ‖ZMod.dft (targetSignal p) k‖ = 1) ∧
    (∀ k, bispectrum (ZMod.dft (targetSignal p)) 0 k =
      bispectrum (ZMod.dft (sourceSignal p)) 0 k) ∧
    (∀ k, bispectrum (ZMod.dft (targetSignal p)) k 1 =
      if k.val < p.1 then 1 else ZMod.stdAddChar (2 : ZMod (order p))) ∧
    (∀ k, ‖bispectrum (ZMod.dft (targetSignal p)) k 1 -
      bispectrum (ZMod.dft (sourceSignal p)) k 1‖ ≤ observationTolerance p) ∧
    0 < observationTolerance p ∧ observationTolerance p ≤ 1 / 4 ∧
    _root_.D5.S3.Fourier.GeneratorRowStability.sourceEnergy (sourceSignal p) = ((order p : ℝ) - 1) / (order p : ℝ) ∧
    (∀ t, R.readout () p t =
      if t = 1 ∨ t = -1 then 1 else 2) ∧
    (∀ K : ℝ, (∃ t : ZMod (order p),
      countingError (sourceSignal p) (targetSignal p) t ≤
        K * observationTolerance p ^ 2 * _root_.D5.S3.Fourier.GeneratorRowStability.sourceEnergy (sourceSignal p)) →
      (order p : ℝ) ^ 3 / (16 * Real.pi ^ 2 * ((order p : ℝ) - 1)) ≤ K ∧
        (order p : ℝ) ^ 2 / (16 * Real.pi ^ 2) <
          (order p : ℝ) ^ 3 / (16 * Real.pi ^ 2 * ((order p : ℝ) - 1)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Parameter := ⟨32, by norm_num⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, herr, _⟩ := h p
  have h1 := herr 1
  norm_num [rejected, realize] at h1

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let p : Parameter := ⟨32, by norm_num⟩
  refine ⟨p, 1, 0, ?_⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, herr, _⟩ := parameter_family p
  change countingError (sourceSignal p) (targetSignal p) 1 ≠
    countingError (sourceSignal p) (targetSignal p) 0
  rw [herr 1, herr 0]
  norm_num [p, order]
  decide

def registration : Registration arena (type_of% (@parameter_family)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@parameter_family, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@parameter_family)
    (type_of% (realize signature
      (fun _ p t => countingError (sourceSignal p) (targetSignal p) t)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Fourier.GeneratorRowOrderNecessity.parameter_family.information_unit,
  realizationName := `Reg.D5.S3.Fourier.GeneratorRowOrderNecessity.registration,
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
    (fun _ p t => countingError (sourceSignal p) (targetSignal p) t)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.GeneratorRowOrderNecessity,
    definition := none,
    coordinates := #[0],
    readouts := #[{
      path := #[
        "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "fn", "arg", "body", "fn", "arg"],
      stateBinder := 1,
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

end Reg.D5.S3.Fourier.GeneratorRowOrderNecessity
end
