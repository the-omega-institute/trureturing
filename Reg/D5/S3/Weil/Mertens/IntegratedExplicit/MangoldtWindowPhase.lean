import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtWindowPhase
import Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows

/-! Source correspondence for the subcritical window obstruction and its RH-conditional input. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (G)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtWindowPhase
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtPointwiseWindows (actual signature)
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtWindowPhase

def arena : Arena where
  signature := signature
  Law V := ∀ {C b : ℝ}, C < firstLiMass → 1 < b →
    ¬ (∀ R : ℝ, ∃ Y ≥ max R 2, ∀ x ∈ Icc Y (Y ^ b), V.readout () () x ≤ C * Real.sqrt x)

private def changed : Realization signature :=
  realize signature (fun _ _ x => (firstLiMass - 1) * Real.sqrt x) (fun e => nomatch e)

private theorem changed_fails : ¬ arena.Law changed := by
  intro h
  apply h (C := firstLiMass - 1) (b := 2) (by linarith) (by norm_num)
  exact fun R => ⟨max R 2, le_rfl, fun _ _ => le_rfl⟩

def evidence : Registration arena (type_of% @no_windows_below_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@no_windows_below_mass, changed, changed_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual changed changed_fails
  dependence := MangoldtPointwiseWindows.Power.evidence.dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@no_windows_below_mass) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtWindowPhase.no_windows_below_mass
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtWindowPhase.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => U x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtWindowPhase
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg",
        "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace ConditionalPeak

def response : Realization signature :=
  realize signature (fun _ _ y => G y) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := RiemannHypothesis → ∀ {δ : ℝ}, 0 < δ →
    ∃ L : ℕ, ∀ n : ℕ, ∃ k ≤ L, |V.readout () () ((n + k : ℕ) : ℝ) - firstLiMass| < δ

private theorem source_bridge :
    (type_of% @bounded_gap_actual_G_peak) ↔ arena.Law response := Iff.rfl

/-- A rejected whole family with the unchanged arithmetic antecedent would prove RH. -/
private theorem rejected_law_implies_rh (V : Realization signature) (hv : ¬ arena.Law V) :
    RiemannHypothesis := by
  by_contra hneg
  exact hv (fun hrh => (hneg hrh).elim)

end ConditionalPeak

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtWindowPhase
