/- GID: D5/S3/ConceptDynamics/Reporting/TruthfulReportBlocksInvertedSpectrum
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Reporting/TruthfulReportBlocksInvertedSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact public recovery forces phenomenal agreement; an inverted pair refutes it. -/

import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'truthful_public_report_forces_phenomenal_agreement' D5
     Golden/Frozen/accepted` returned no hit.
   * The requested structural search found `LanguagePostprocessingObstruction` and
     `HistorySensitiveOutcomeReductionObstruction`. Both prove non-recovery from a
     fiber collision, whereas this module assumes recovery and derives fiber constancy.
   * `TruthfulnessSufficiencyIndependence` separates honesty from target sufficiency;
     it has neither the inverted-pair contrapositive nor the required Bool/Unit witness.
   * Pinned Mathlib's `Function.factorsThrough_iff` identifies recovery factorization
     with `Function.FactorsThrough`; its factorization-to-fiber direction is reused.
   * No repository theorem combines that positive direction, the single premise-failure
     proposition, and the concrete inverted-spectrum witness, so this is not an alias. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Reporting.TruthfulReportBlocksInvertedSpectrum

/-- Exact truthful public reporting means that a public value determines a recoverable
phenomenal value, including on every public value outside the realized image. -/
def TruthfulPublicReport {State Phenomenal Public : Type*}
    (phenomenal : State -> Phenomenal) (publicReadout : State -> Public) : Prop :=
  ∃ recover : Public -> Phenomenal, phenomenal = recover ∘ publicReadout

/-- Exact recovery from the public readout makes the phenomenal readout constant on
every public fiber. -/
theorem truthful_public_report_forces_phenomenal_agreement
    {State Phenomenal Public : Type*}
    (phenomenal : State -> Phenomenal) (publicReadout : State -> Public)
    (truthful : TruthfulPublicReport phenomenal publicReadout) (x y : State) :
    publicReadout x = publicReadout y -> phenomenal x = phenomenal y := by
  intro samePublic
  letI : Nonempty Phenomenal := ⟨phenomenal x⟩
  exact
    ((Function.factorsThrough_iff (f := publicReadout) phenomenal).2 truthful) samePublic

/- The source's five failure modes are alternative explanations of one failed
truthful-report premise. They are therefore represented by the single negation below,
not by five independently provable structures. -/

/-- A phenomenally different but publicly equivalent pair refutes constancy on all
public fibers, so at least one explanation of truthful-report failure is unavoidable. -/
theorem inverted_spectrum_requires_premise_failure
    {State Phenomenal Public : Type*}
    (phenomenal : State -> Phenomenal) (publicReadout : State -> Public) (x y : State) :
    phenomenal x ≠ phenomenal y -> publicReadout x = publicReadout y ->
      ¬(∀ a b, publicReadout a = publicReadout b -> phenomenal a = phenomenal b) := by
  intro differentPhenomenal samePublic constantOnPublicFibers
  exact differentPhenomenal (constantOnPublicFibers x y samePublic)

/-- A two-state phenomenal readout that preserves the Boolean distinction. -/
def invertedPhenomenal : Bool -> Bool := id

/-- A public readout that collapses both Boolean states to the same observation. -/
def invertedPublic : Bool -> Unit := fun _ => ()

example :
    invertedPublic false = invertedPublic true ∧
      invertedPhenomenal false ≠ invertedPhenomenal true ∧
        (¬(∀ a b, invertedPublic a = invertedPublic b ->
          invertedPhenomenal a = invertedPhenomenal b)) ∧
          ¬TruthfulPublicReport invertedPhenomenal invertedPublic := by
  refine ⟨rfl, Bool.false_ne_true, ?_, ?_⟩
  · exact inverted_spectrum_requires_premise_failure
      invertedPhenomenal invertedPublic false true Bool.false_ne_true rfl
  · intro truthful
    exact Bool.false_ne_true
      (truthful_public_report_forces_phenomenal_agreement
        invertedPhenomenal invertedPublic truthful false true rfl)

#print axioms truthful_public_report_forces_phenomenal_agreement

end D5.S3.ConceptDynamics.Reporting.TruthfulReportBlocksInvertedSpectrum
