import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyOddWrapSecondOrderThresholdBracket
import Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapThresholdBracket
import Reg.Support.DependentFamily

/-! Registration for the complete original
single-crossing criterion with its K=1 second-order threshold bracket.

Reuse the coarse bracket's native Nat-valued signature, actual family,
whole-role zero interventions and actual observational dependence. States
remain every natural t>=2; no Gaussian band restriction is imposed here.
The Law retains the unique T>2, every before/at/after comparison, the
strict corrected lower bound and the corrected integer-ceiling upper bound.
Rejection uses each proposed Law's own threshold, never an assumed actual T.

Source-occurrence binding remains unfinished under
https://github.com/the-omega-institute/trureturing/issues/25856 .
sourceSelection and familyRecord remain none; continuation is unknown.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapSecondOrderThresholdBracket

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapSecondOrderThresholdBracket
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapThresholdBracket
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev secondOrderThresholdBracketArena : Arena where
  signature := thresholdBracketSignature
  Law R := ∀ (p : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p),
    let pp : thresholdBracketSignature.Params := ⟨p,hp5,hpo⟩
    ∃! T : ℕ, ∃ hT : 2 < T,
      (∀ (t : ℕ) (ht2 : 2 ≤ t), t < T →
        R.readout 1 pp ⟨t,ht2⟩ < R.readout 0 pp ⟨t,ht2⟩) ∧
      R.readout 0 pp ⟨T,hT.le⟩ ≤ R.readout 1 pp ⟨T,hT.le⟩ ∧
      (∀ (t : ℕ) (hTt : T < t),
        R.readout 0 pp ⟨t,(hT.trans hTt).le⟩ <
          R.readout 1 pp ⟨t,(hT.trans hTt).le⟩) ∧
      alpha*(p : ℝ)+1/6+beta_correction/(p : ℝ)-1/(p : ℝ)^3 < (T : ℝ) ∧
      (T : ℤ) ≤ Int.ceil
        (alpha*(p : ℝ)+1/6+beta_correction/(p : ℝ)+1/(p : ℝ)^3)

private theorem secondOrderThresholdBracket_actual_bridge :
    (type_of% actual_odd_wrap_second_order_threshold_bracket) ↔
      secondOrderThresholdBracketArena.Law thresholdBracketActual := by
  simp [secondOrderThresholdBracketArena, thresholdBracketActual, realize,
    and_assoc, and_left_comm, and_comm]

private theorem secondOrderThresholdBracket_actual_law :
    secondOrderThresholdBracketArena.Law thresholdBracketActual :=
  secondOrderThresholdBracket_actual_bridge.mp actual_odd_wrap_second_order_threshold_bracket

private theorem secondOrderThresholdBracket_rejected_law (i : Fin 2) :
    ¬ secondOrderThresholdBracketArena.Law (thresholdBracketRejected i) := by
  intro h
  obtain ⟨T,hT,_⟩ := h 5 (by norm_num) (by decide)
  obtain ⟨hT2,hbefore,hmid,hafter,hlower,hupper⟩ := hT
  fin_cases i
  · have hh := hbefore 2 (by norm_num) hT2
    have hh' : (original_return_pair 5 2).2 < 0 := by
      simpa [thresholdBracketRejected, thresholdBracketActual, realize] using hh
    omega
  · have hh := hafter (T+1) (by omega)
    have hh' : (original_return_pair 5 ((T+1 : ℕ) : ℤ)).1 < 0 := by
      simpa [thresholdBracketRejected, thresholdBracketActual, realize] using hh
    omega

noncomputable def secondOrderThresholdBracketSource : Registration
    secondOrderThresholdBracketArena
    (type_of% actual_odd_wrap_second_order_threshold_bracket) where
  actual := thresholdBracketActual
  bridge := secondOrderThresholdBracket_actual_bridge
  variation := ⟨secondOrderThresholdBracket_actual_law,
    thresholdBracketRejected 0, secondOrderThresholdBracket_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨thresholdBracketRejected i, ?_, rfl, secondOrderThresholdBracket_rejected_law i⟩
      intro j hj
      funext p t
      simp [thresholdBracketRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := thresholdBracketSource.dependence

noncomputable def secondOrderThresholdBracketRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_odd_wrap_second_order_threshold_bracket)
      (Realization thresholdBracketSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapSecondOrderThresholdBracket.actual_odd_wrap_second_order_threshold_bracket.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapSecondOrderThresholdBracket.secondOrderThresholdBracketSource
  realizationSource := none
  generated := false
  arena := .source ⟨secondOrderThresholdBracketArena⟩
  objectArena := .source ⟨secondOrderThresholdBracketArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source secondOrderThresholdBracketArena ⟨secondOrderThresholdBracketSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some thresholdBracketActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapSecondOrderThresholdBracket
