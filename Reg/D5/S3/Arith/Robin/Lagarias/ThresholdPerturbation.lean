import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Lagarias.ThresholdPerturbation
import Reg.Support.SingleDependentReadout
import Mathlib.Tactic.NormNum

/-! A source-bound family for the harmonic threshold.
Four-slot source-selection evidence remains unregistered. -/

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

end Reg.D5.S3.Arith.Robin.Lagarias.ThresholdPerturbation
