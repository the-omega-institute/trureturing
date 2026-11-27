import D5.S3.Arith.Robin.PriceRecord.ExactCutoff.ExactRationalCutoffSeparation
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Tactic.NormNum
import Reg.Support.DependentFamily

/-! Source-bound registration of the finite rational cutoff separation bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ExactCutoff.ExactRationalCutoffSeparation

open LeanInformationAudit
open _root_.D5.S3.Arith.Robin.PriceRecord.ExactCutoff.ExactRationalCutoffSeparation (cutoff_resonance_separation)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Replace the observed log gap by zero at every mode. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

noncomputable section

def actual : Realization signature :=
  realize signature (fun _ q j =>
    |(q.2.2 : ℝ) * Real.log (2 * (q.1 : ℝ) / ((q.1 : ℝ) + q.2.1)) -
      (q.2.1 : ℝ) * Real.log ((j : ℝ) * q.1 / ((q.1 : ℝ) + q.2.2))|)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m h p j : ℕ} (_hh : 0 < h) (_hhm : h < m)
    (_hhp : h < p) (_hp3 : p < 3 * h) (_hj : 0 < j),
    let U : ℕ := 2 ^ p * m ^ (p - h) * (m + p) ^ h
    let W : ℕ := j ^ h * (m + h) ^ p
    U ≠ W ∧ 1 / ((max U W : ℕ) : ℝ) ≤ R.readout () ⟨m, ⟨h, p⟩⟩ j

private theorem source_bridge :
    (type_of% (@cutoff_resonance_separation)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbound := (h (m := 2) (h := 1) (p := 2) (j := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide)).2
  change (1 : ℝ) / ((max (32 : ℕ) 18 : ℕ) : ℝ) ≤ 0 at hbound
  norm_num [max_def] at hbound

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, ⟨1, 2⟩⟩, 1, 2, ?_⟩
  simp only [actual, realize, Nat.cast_ofNat, Nat.cast_one]
  have hbase : 0 < (2 : ℝ) * Real.log (2 * 2 / (2 + 1)) :=
    mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hhalf : Real.log ((2 : ℝ) / (2 + 2)) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  have hone : Real.log ((2 : ℝ) * 2 / (2 + 2)) = 0 := by
    rw [show (2 : ℝ) * 2 / (2 + 2) = 1 by norm_num, Real.log_one]
  have hlt : (2 : ℝ) * Real.log (2 * 2 / (2 + 1)) <
      2 * Real.log (2 * 2 / (2 + 1)) - Real.log (2 / (2 + 2)) := by
    simpa only [sub_zero] using sub_lt_sub_left hhalf ((2 : ℝ) * Real.log (2 * 2 / (2 + 1)))
  simpa only [one_mul, hone, sub_zero, abs_of_pos hbase,
    abs_of_pos (sub_pos.mpr (hhalf.trans hbase))] using hlt.ne'

def family : Registration arena (type_of% (@cutoff_resonance_separation)) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@cutoff_resonance_separation), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cutoff_resonance_separation) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ExactCutoff.ExactRationalCutoffSeparation.cutoff_resonance_separation.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ExactCutoff.ExactRationalCutoffSeparation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q j =>
    |(q.2.2 : ℝ) * Real.log (2 * (q.1 : ℝ) / ((q.1 : ℝ) + q.2.1)) -
      (q.2.1 : ℝ) * Real.log ((j : ℝ) * q.1 / ((q.1 : ℝ) + q.2.2))|)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  -- Four natural variables, five hypotheses, then the lets U and W.
  -- Select the right conjunct and the right operand of LE.le.
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ExactCutoff.ExactRationalCutoffSeparation
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Arith.Robin.PriceRecord.ExactCutoff.ExactRationalCutoffSeparation
