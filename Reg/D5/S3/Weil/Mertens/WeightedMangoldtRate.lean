import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.WeightedMangoldtRate
import Reg.Support.SingleDependentReadout
noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Weil.Mertens.WeightedMangoldtRate

namespace RetainedWeightedTail
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ {c D X x : ℝ} (hc : 0 < c) (hD : 0 ≤ D)
    (hX : 2 ≤ X) (hx : X ≤ x)
    (hpsi : ∀ u ≥ X, |Chebyshev.psi u - u| ≤
      D * (u * _root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.rate (2 * c) u)),
    |∫ u in Ioi x, (Chebyshev.psi u - u) / u ^ 2| ≤ R.readout () ()
      (D * (∫ u in Ioi 1, _root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.weight c u) *
        _root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.rate c x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c₀, hc₀, hO⟩ := MediumPNT
  obtain ⟨D, hD, hbound⟩ := isBigO_iff'.mp hO
  obtain ⟨A, hA⟩ := eventually_atTop.mp hbound
  let X : ℝ := max A 2
  let c : ℝ := c₀ / 2
  have hX : (2 : ℝ) ≤ X := le_max_right _ _
  have hc : 0 < c := by dsimp [c]; positivity
  have hdouble : 2 * c = c₀ := by dsimp [c]; ring
  have hpsi (u : ℝ) (hu : X ≤ u) : |Chebyshev.psi u - u| ≤
      D * (u * _root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.rate (2 * c) u) := by
    have hu0 : 0 < u := by linarith
    have huA : A ≤ u := (le_max_left A 2).trans hu
    simpa only [_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.rate, hdouble,
      Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_mul, abs_of_pos hu0,
      abs_of_pos (Real.exp_pos _)] using hA u huA
  have h0 := h hc hD.le hX (show X ≤ X from le_rfl) hpsi
  change |∫ u in Ioi X, (Chebyshev.psi u - u) / u ^ 2| ≤ (-1 : ℝ) at h0
  linarith only [h0, abs_nonneg (∫ u in Ioi X, (Chebyshev.psi u - u) / u ^ 2)]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.chebyshev_tail_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.chebyshev_tail_bound, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.chebyshev_tail_bound) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.WeightedMangoldtRate.chebyshev_tail_bound.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.WeightedMangoldtRate.RetainedWeightedTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end RetainedWeightedTail


namespace RetainedWeightedEndpoint
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)
private def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∃ c > 0, ∃ C > 0, ∃ X ≥ (2 : ℝ), ∀ x ≥ X,
    |_root_.Mertens.E₁Λ x + Real.eulerMascheroniConstant| ≤
      R.readout () () (C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, hc, C, hC, X, hX, hb⟩ := h
  have h0 := hb X le_rfl
  change |_root_.Mertens.E₁Λ X + Real.eulerMascheroniConstant| ≤ (-1 : ℝ) at h0
  linarith only [h0, abs_nonneg (_root_.Mertens.E₁Λ X + Real.eulerMascheroniConstant)]
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by change (0 : ℝ) ≠ 1; norm_num⟩
def family : Registration arena (type_of% @_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.E1Lambda_stretched_exponential) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.E1Lambda_stretched_exponential, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Weil.Mertens.WeightedMangoldtRate.E1Lambda_stretched_exponential) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.WeightedMangoldtRate.E1Lambda_stretched_exponential.audit
  realizationName := `Reg.D5.S3.Weil.Mertens.WeightedMangoldtRate.RetainedWeightedEndpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end RetainedWeightedEndpoint


end Reg.D5.S3.Weil.Mertens.WeightedMangoldtRate
