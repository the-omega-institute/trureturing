import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Lagarias.ThresholdPerturbation
import Reg.Support.SingleDependentReadout

/-! Source-bound mathematical audit families for the harmonic threshold and
the full conditional original-record endpoint. Source-selection evidence and
the conditional family's variation remain unregistered. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Lagarias.ThresholdPerturbation

namespace Reg.D5.S3.Arith.Robin.Lagarias.ThresholdPerturbation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

namespace Threshold

def actual : Realization signature :=
  realize signature (fun _ _ n => gap n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := Tendsto (fun n : ℕ => Real.log (n : ℝ) * R.readout () () n) atTop
    (𝓝 (Real.exp Real.eulerMascheroniConstant * Real.eulerMascheroniConstant))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant * Real.eulerMascheroniConstant)) := by
    simpa [arena, rejected, realize] using h
  have he := tendsto_nhds_unique tendsto_const_nhds hh
  have hp : 0 < Real.exp Real.eulerMascheroniConstant * Real.eulerMascheroniConstant :=
    mul_pos (Real.exp_pos _) (by linarith [Real.one_half_lt_eulerMascheroniConstant])
  linarith

def family : Registration arena
    (type_of% (@_root_.D5.S3.Arith.Robin.Lagarias.ThresholdPerturbation.threshold_asymptotic)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨threshold_asymptotic, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize, gap, threshold]

end Threshold

namespace SharpMargin

open _root_.D5.S3.Arith.GoldenResourceOptimalInteger (goldenResourceObjective)
open _root_.D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin (K)

def actual : Realization signature :=
  realize signature (fun _ _ n => margin n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ _hRH : RiemannHypothesis,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.exp Real.eulerMascheroniConstant * K - ε < R.readout () () n) ∧
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ m : ℕ, ∃ lambda : ℝ,
      N ≤ m ∧ 0 < lambda ∧ 2 ≤ m ∧
      (∀ k : ℕ, 0 < k → k < m →
        goldenResourceObjective lambda k < goldenResourceObjective lambda m) ∧
      |R.readout () () m - Real.exp Real.eulerMascheroniConstant * K| < ε) ∧
    Filter.liminf (R.readout () ()) atTop = Real.exp Real.eulerMascheroniConstant * K

private theorem actual_law : arena.Law actual := @sharp_lagarias_margin

private theorem source_bridge :
    (type_of% (@_root_.D5.S3.Arith.Robin.Lagarias.ThresholdPerturbation.sharp_lagarias_margin)) ↔
      arena.Law actual := Iff.rfl

private theorem rejection_requires_rh (bad : Realization signature)
    (hbad : ¬ arena.Law bad) : RiemannHypothesis := by
  classical
  by_contra hnot
  apply hbad
  intro hRH
  exact (hnot hRH).elim

end SharpMargin

end Reg.D5.S3.Arith.Robin.Lagarias.ThresholdPerturbation
