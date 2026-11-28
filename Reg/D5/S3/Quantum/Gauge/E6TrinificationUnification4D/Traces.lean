import Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Common

/-! Typed source observations and whole-family interventions. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.E6TrinificationUnification4D
open _root_.Reg.Support.SingleDependentReadout (signature)
open LeanInformationAudit
open _root_.D5.S3.Quantum.Gauge
open scoped BigOperators InnerProductSpace

namespace Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Traces
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev linearSignature : Signature := signature Unit (fun _ => E6Rep27) (fun _ => ℝ)

abbrev linearArena : Arena where
  signature := linearSignature
  Law R := (∑ s : E6Rep27, R.readout () () s) = 0 ∧ (∑ s : E6Rep27, T3 s) = 0 ∧
    (∑ s : E6Rep27, Q s) = 0 ∧ (∑ s : E6Rep27, qPsi s) = 0 ∧
    (∑ s : E6Rep27, qChi s) = 0 ∧ (∑ s : E6Rep27, bMinusL s) = 0

def linearFamily : Registration linearArena (type_of% (@linear_traces)) :=
  e6Family% linearArena (@linear_traces) (realize linearSignature (fun _ _ s => Y s) (fun e => nomatch e))
    (by
      refine ⟨(), fundamental 0, neutral, ?_⟩
      norm_num [realize, fundamental, neutral, Y, T3, Q, qPsi, qChi, bMinusL, cartanWeight,
      SU5SO10GrandUnification4D.hyperchargeWeights,
      SU5SO10GrandUnification4D.weakWeights, colorCubic, colorIndex, colorSector])
    (realize linearSignature (fun _ _ _ => 1) (fun e => nomatch e))
    (by
      intro h
      have hh := h.1
      change (∑ _ : E6Rep27, (1 : ℝ)) = 0 at hh
      norm_num [Fintype.card_sum] at hh)

def linearRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@linear_traces) (Realization linearSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.linear_traces.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Traces.linearFamily
    linearArena linearFamily (realize linearSignature (fun _ _ s => Y s) (fun e => nomatch e))
    #[] (e6Path% linear_traces Y 1 0) 0 false none

abbrev orthogonalSignature : Signature := signature Unit (fun _ => E6Rep27) (fun _ => ℝ)

abbrev orthogonalArena : Arena where
  signature := orthogonalSignature
  Law R := (∑ s : E6Rep27, R.readout () () s) = 0 ∧
    (∑ s : E6Rep27, Y s * qPsi s) = 0 ∧
    (∑ s : E6Rep27, Y s * qChi s) = 0 ∧
    (∑ s : E6Rep27, T3 s * qPsi s) = 0 ∧
    (∑ s : E6Rep27, T3 s * qChi s) = 0 ∧
    (∑ s : E6Rep27, qPsi s * qChi s) = 0

def orthogonalFamily : Registration orthogonalArena (type_of% (@pairwise_orthogonality)) :=
  e6Family% orthogonalArena (@pairwise_orthogonality) (realize orthogonalSignature (fun _ _ s => Y s * T3 s) (fun e => nomatch e))
    (by
      refine ⟨(), fundamental 3, neutral, ?_⟩
      norm_num [realize, fundamental, neutral, Y, T3, Q, qPsi, qChi, bMinusL, cartanWeight,
      SU5SO10GrandUnification4D.hyperchargeWeights,
      SU5SO10GrandUnification4D.weakWeights, colorCubic, colorIndex, colorSector])
    (realize orthogonalSignature (fun _ _ _ => 1) (fun e => nomatch e))
    (by
      intro h
      have hh := h.1
      change (∑ _ : E6Rep27, (1 : ℝ)) = 0 at hh
      norm_num [Fintype.card_sum] at hh)

def orthogonalRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pairwise_orthogonality) (Realization orthogonalSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.pairwise_orthogonality.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Traces.orthogonalFamily
    orthogonalArena orthogonalFamily (realize orthogonalSignature (fun _ _ s => Y s * T3 s) (fun e => nomatch e))
    #[] (e6Path% pairwise_orthogonality HMul.hMul 6 0) 0 false none

abbrev quadraticSignature : Signature := signature Unit (fun _ => E6Rep27) (fun _ => ℝ)

abbrev quadraticArena : Arena where
  signature := quadraticSignature
  Law R := (∑ s : E6Rep27, R.readout () () s) = 3 ∧ (∑ s : E6Rep27, (Y s)^2) = 5 ∧
    (∑ s : E6Rep27, (Q s)^2) = 8 ∧ (∑ s : E6Rep27, (qPsi s)^2) = 72 ∧
    (∑ s : E6Rep27, (qChi s)^2) = 120

def quadraticFamily : Registration quadraticArena (type_of% (@quadratic_traces)) :=
  e6Family% quadraticArena (@quadratic_traces) (realize quadraticSignature (fun _ _ s => (T3 s)^2) (fun e => nomatch e))
    (by
      refine ⟨(), fundamental 3, neutral, ?_⟩
      norm_num [realize, fundamental, neutral, Y, T3, Q, qPsi, qChi, bMinusL, cartanWeight,
      SU5SO10GrandUnification4D.hyperchargeWeights,
      SU5SO10GrandUnification4D.weakWeights, colorCubic, colorIndex, colorSector])
    (realize quadraticSignature (fun _ _ _ => 1) (fun e => nomatch e))
    (by
      intro h
      have hh := h.1
      change (∑ _ : E6Rep27, (1 : ℝ)) = 3 at hh
      norm_num [Fintype.card_sum] at hh)

def quadraticRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@quadratic_traces) (Realization quadraticSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.quadratic_traces.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Traces.quadraticFamily
    quadraticArena quadraticFamily (realize quadraticSignature (fun _ _ s => (T3 s)^2) (fun e => nomatch e))
    #[] (e6Path% quadratic_traces HPow.hPow 6 0) 0 false none

abbrev ratioSignature : Signature := signature Unit (fun _ => E6Rep27) (fun _ => ℝ)

abbrev ratioArena : Arena where
  signature := ratioSignature
  Law R := (∑ s : E6Rep27, R.readout () () s) / (∑ s : E6Rep27, (Q s)^2) = 3/8

def ratioFamily : Registration ratioArena (type_of% (@weinberg_trace_ratio)) :=
  e6Family% ratioArena (@weinberg_trace_ratio) (realize ratioSignature (fun _ _ s => (T3 s)^2) (fun e => nomatch e))
    (by
      refine ⟨(), fundamental 3, neutral, ?_⟩
      norm_num [realize, fundamental, neutral, Y, T3, Q, qPsi, qChi, bMinusL, cartanWeight,
      SU5SO10GrandUnification4D.hyperchargeWeights,
      SU5SO10GrandUnification4D.weakWeights, colorCubic, colorIndex, colorSector])
    (realize ratioSignature (fun _ _ _ => 1) (fun e => nomatch e))
    (by
      intro h
      change (∑ _ : E6Rep27, (1 : ℝ)) / (∑ s : E6Rep27, (Q s)^2) = 3/8 at h
      rw [quadratic_traces.2.2.1] at h
      norm_num [Fintype.card_sum] at h)

def ratioRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weinberg_trace_ratio) (Realization ratioSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.weinberg_trace_ratio.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Traces.ratioFamily
    ratioArena ratioFamily (realize ratioSignature (fun _ _ s => (T3 s)^2) (fun e => nomatch e))
    #[] (e6Path% weinberg_trace_ratio HPow.hPow 6 0) 0 false none

abbrev colorAnomaliesSignature : Signature := signature Unit (fun _ => E6Rep27) (fun _ => ℝ)

abbrev colorAnomaliesArena : Arena where
  signature := colorAnomaliesSignature
  Law R := (∑ s : E6Rep27, R.readout () () s) = 0 ∧
    ∀ a b c d : ℝ,
      (∑ s : E6Rep27, colorIndex s * (a*Y s+b*T3 s+c*qPsi s+d*qChi s)) = 0

def colorAnomaliesFamily : Registration colorAnomaliesArena (type_of% (@color_anomalies)) :=
  e6Family% colorAnomaliesArena (@color_anomalies) (realize colorAnomaliesSignature (fun _ _ s => colorCubic s) (fun e => nomatch e))
    (by
      refine ⟨(), fundamental 0, neutral, ?_⟩
      norm_num [realize, fundamental, neutral, Y, T3, Q, qPsi, qChi, bMinusL, cartanWeight,
      SU5SO10GrandUnification4D.hyperchargeWeights,
      SU5SO10GrandUnification4D.weakWeights, colorCubic, colorIndex, colorSector])
    (realize colorAnomaliesSignature (fun _ _ _ => 1) (fun e => nomatch e))
    (by
      intro h
      have hh := h.1
      change (∑ _ : E6Rep27, (1 : ℝ)) = 0 at hh
      norm_num [Fintype.card_sum] at hh)

def colorAnomaliesRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@color_anomalies) (Realization colorAnomaliesSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.color_anomalies.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Traces.colorAnomaliesFamily
    colorAnomaliesArena colorAnomaliesFamily (realize colorAnomaliesSignature (fun _ _ s => colorCubic s) (fun e => nomatch e))
    #[] (e6Path% color_anomalies colorCubic 1 0) 0 false none

end
end Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Traces
