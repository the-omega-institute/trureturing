import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.CenteredTail
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Weil.Mertens.CenteredTail

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.CenteredTail
open LeanInformationAudit Real Filter Asymptotics
open scoped Topology

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => _root_.Mertens.E₂p x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := (fun x : ℝ => R.readout () () x) =o[atTop] (fun x : ℝ => 1 / log x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) :=
    h.trans_tendsto (by simpa only [one_div] using Real.tendsto_log_atTop.inv_tendsto_atTop)
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at he

def family : Registration arena (type_of% E2p_isLittleO_inv_log) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨E2p_isLittleO_inv_log, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), Real.exp (-2), ?_⟩
    change _root_.Mertens.E₂p 0 ≠ _root_.Mertens.E₂p (Real.exp (-2))
    have hfloor : ⌊Real.exp (-2)⌋₊ = 0 := Nat.floor_eq_zero.mpr
      (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (-2 : ℝ) < 0))
    simp only [_root_.Mertens.E₂p, hfloor, Nat.floor_zero, Finset.Ioc_self,
      Finset.filter_empty, Finset.sum_empty, Real.log_zero, sub_self, zero_sub,
      Real.log_exp]
    have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.log_neg_eq_log]
    linarith

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@E2p_isLittleO_inv_log) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.CenteredTail.E2p_isLittleO_inv_log.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.CenteredTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => _root_.Mertens.E₂p x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.CenteredTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Weil.Mertens.CenteredTail
