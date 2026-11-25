import D5.S3.Arith.FactorialRatio.Compression.StirlingBarrier
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FactorialRatio.Compression.StirlingBarrier

open Finset Real
open LeanInformationAudit
open _root_.D5.S3.Arith.FactorialRatio.CompactFactorialGcd
open _root_.D5.S3.Arith.FactorialRatio.Compression.StirlingBarrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ) (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ p b => selbergFactorial p.1 p.2 b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r s b : ℕ), r * b ≤ s →
    |log (R.readout () (r, s) b : ℝ) -
      ((r : ℝ) * s * (log s - 1) + (r : ℝ) * b * log r -
        (s : ℝ) * ∑ i ∈ range r, Real.binEntropy (((i * b : ℕ) : ℝ) / s))| ≤
      2 * (r : ℝ) * (log ((s : ℝ) + 1) + 1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 0 0 0 (by decide)
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz : Real.log 2 ≤ 0 := by
    simpa [rejected, realize, abs_of_pos hp] using hbad
  exact (not_le_of_gt hp) hz

def family : Registration arena (type_of% @compact_stirling_entropy_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨compact_stirling_entropy_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    refine ⟨(2, 3), 0, 1, ?_⟩
    change selbergFactorial 2 3 0 ≠ selbergFactorial 2 3 1
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@compact_stirling_entropy_bound) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.Compression.StirlingBarrier.compact_stirling_entropy_bound.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.Compression.StirlingBarrier.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p b => selbergFactorial p.1 p.2 b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.Compression.StirlingBarrier
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "arg", "arg", "fn"]
      stateBinder := 2
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FactorialRatio.Compression.StirlingBarrier
