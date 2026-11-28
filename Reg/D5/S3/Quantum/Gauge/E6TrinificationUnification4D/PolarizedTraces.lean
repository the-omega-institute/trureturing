import Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Common

/-! Typed source observations and whole-family interventions. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.E6TrinificationUnification4D
open _root_.Reg.Support.SingleDependentReadout (signature)
open LeanInformationAudit
open _root_.D5.S3.Quantum.Gauge
open scoped BigOperators InnerProductSpace

namespace Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.PolarizedTraces
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev pairingSignature : Signature := signature (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => E6Rep27) (fun _ => ℝ)

abbrev pairingArena : Arena where
  signature := pairingSignature
  Law R := ∀ (a b c d e f g h : ℝ),
    (∑ s : E6Rep27, (R.readout () ⟨a, b, c, d⟩ s) *
      (e*Y s+f*T3 s+g*qPsi s+h*qChi s)) = 5*a*e+3*b*f+72*c*g+120*d*h

def pairingFamily : Registration pairingArena (type_of% (@trace_pairing)) :=
  e6Family% pairingArena (@trace_pairing) (realize pairingSignature (fun _ p s => p.1*Y s+p.2.1*T3 s+p.2.2.1*qPsi s+p.2.2.2*qChi s) (fun e => nomatch e))
    (by
      refine ⟨⟨1, 0, 0, 0⟩, fundamental 0, neutral, ?_⟩
      norm_num [realize, fundamental, neutral, Y, T3, Q, qPsi, qChi, bMinusL, cartanWeight,
      SU5SO10GrandUnification4D.hyperchargeWeights,
      SU5SO10GrandUnification4D.weakWeights, colorCubic, colorIndex, colorSector])
    (realize pairingSignature (fun _ _ _ => 1) (fun e => nomatch e))
    (by
      intro h
      have hh := h 1 0 0 0 1 0 0 0
      change (∑ s : E6Rep27, 1 * (1*Y s+0*T3 s+0*qPsi s+0*qChi s)) = _ at hh
      simp only [one_mul, zero_mul, add_zero] at hh
      rw [linear_traces.1] at hh
      norm_num at hh)

def pairingRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trace_pairing) (Realization pairingSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.trace_pairing.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.PolarizedTraces.pairingFamily
    pairingArena pairingFamily (realize pairingSignature (fun _ p s => p.1*Y s+p.2.1*T3 s+p.2.2.1*qPsi s+p.2.2.2*qChi s) (fun e => nomatch e))
    #[0, 1, 2, 3] (e6Path% trace_pairing HAdd.hAdd 6 0) 8 false none

abbrev cubicSignature : Signature := signature (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => E6Rep27) (fun _ => ℝ)

abbrev cubicArena : Arena where
  signature := cubicSignature
  Law R := ∀ (a b c d : ℝ),
    (∑ s : E6Rep27, (R.readout () ⟨a, b, c, d⟩ s)^3) = 0

def cubicFamily : Registration cubicArena (type_of% (@universal_abelian_cubic)) :=
  e6Family% cubicArena (@universal_abelian_cubic) (realize cubicSignature (fun _ p s => p.1*Y s+p.2.1*T3 s+p.2.2.1*qPsi s+p.2.2.2*qChi s) (fun e => nomatch e))
    (by
      refine ⟨⟨1, 0, 0, 0⟩, fundamental 0, neutral, ?_⟩
      norm_num [realize, fundamental, neutral, Y, T3, Q, qPsi, qChi, bMinusL, cartanWeight,
      SU5SO10GrandUnification4D.hyperchargeWeights,
      SU5SO10GrandUnification4D.weakWeights, colorCubic, colorIndex, colorSector])
    (realize cubicSignature (fun _ _ _ => 1) (fun e => nomatch e))
    (by
      intro h
      have hh := h 0 0 0 0
      change (∑ _ : E6Rep27, (1 : ℝ)^3) = 0 at hh
      norm_num [Fintype.card_sum] at hh)

def cubicRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@universal_abelian_cubic) (Realization cubicSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.universal_abelian_cubic.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.PolarizedTraces.cubicFamily
    cubicArena cubicFamily (realize cubicSignature (fun _ p s => p.1*Y s+p.2.1*T3 s+p.2.2.1*qPsi s+p.2.2.2*qChi s) (fun e => nomatch e))
    #[0, 1, 2, 3] (e6Path% universal_abelian_cubic HAdd.hAdd 6 0) 4 false none

abbrev mixedSignature : Signature := signature (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℝ, ℝ) (fun _ => E6Rep27) (fun _ => ℝ)

abbrev mixedArena : Arena where
  signature := mixedSignature
  Law R := ∀ (a b c d e f g h i j k l : ℝ),
    (∑ s : E6Rep27,
      (R.readout () ⟨a, b, c, d⟩ s) *
      (e*Y s+f*T3 s+g*qPsi s+h*qChi s) *
      (i*Y s+j*T3 s+k*qPsi s+l*qChi s)) = 0

def mixedFamily : Registration mixedArena (type_of% (@mixed_abelian_cubic)) :=
  e6Family% mixedArena (@mixed_abelian_cubic) (realize mixedSignature (fun _ p s => p.1*Y s+p.2.1*T3 s+p.2.2.1*qPsi s+p.2.2.2*qChi s) (fun e => nomatch e))
    (by
      refine ⟨⟨1, 0, 0, 0⟩, fundamental 0, neutral, ?_⟩
      norm_num [realize, fundamental, neutral, Y, T3, Q, qPsi, qChi, bMinusL, cartanWeight,
      SU5SO10GrandUnification4D.hyperchargeWeights,
      SU5SO10GrandUnification4D.weakWeights, colorCubic, colorIndex, colorSector])
    (realize mixedSignature (fun _ _ _ => 1) (fun e => nomatch e))
    (by
      intro h
      have hh := h 0 0 0 0 1 0 0 0 1 0 0 0
      change (∑ s : E6Rep27, 1 * (1*Y s+0*T3 s+0*qPsi s+0*qChi s) * (1*Y s+0*T3 s+0*qPsi s+0*qChi s)) = 0 at hh
      simp only [one_mul, zero_mul, add_zero, ← pow_two] at hh
      rw [quadratic_traces.2.1] at hh
      norm_num at hh)

def mixedRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mixed_abelian_cubic) (Realization mixedSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.mixed_abelian_cubic.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.PolarizedTraces.mixedFamily
    mixedArena mixedFamily (realize mixedSignature (fun _ p s => p.1*Y s+p.2.1*T3 s+p.2.2.1*qPsi s+p.2.2.2*qChi s) (fun e => nomatch e))
    #[0, 1, 2, 3] (e6Path% mixed_abelian_cubic HAdd.hAdd 6 0) 12 false none

end
end Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.PolarizedTraces
