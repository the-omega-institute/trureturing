import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.CriticalThetaTailPeak
import Reg.Support.SingleDependentReadout

/-! The complete original law observes the actual signed tail. Its zero-output
intervention is rejected exactly when a genuine zero in the specified open
strip exists; no such zero is introduced as audit evidence. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Complex
open _root_.D5.S3.Weil.Mertens.CriticalThetaTailPeak
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.CriticalThetaTailPeak

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ → ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ f u => f u) (fun e => nomatch e)

def zeroTail : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law Q := ∀ {ρ : ℂ}, (1 / 2 : ℝ) < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 →
    let m := analyticOrderNatAt riemannZeta ρ
    0 < m ∧ ρ.im ≠ 0 ∧
      ∀ c : ℝ, 0 ≤ c → c < (m : ℝ) / (‖ρ‖ * ‖ρ - 1‖) →
        ∀ T : ℝ, ∃ u : ℝ, max T (Real.log 2) < u ∧
          c < u * Real.exp ((1 - ρ.re) * u) *
            Q.readout () _root_.D5.S3.Weil.Mertens.ActualThetaTailLaplace.f u

private theorem actual_law : arena.Law actual := @critical_theta_tail_peak

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨id, 0, 1, zero_ne_one⟩

private theorem rejected_requires_zero {Q : Realization signature} (hQ : ¬ arena.Law Q) :
    ∃ ρ : ℂ, (1 / 2 : ℝ) < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 := by
  by_contra hzero
  apply hQ
  intro ρ hβ hβ1 hz
  exact (hzero ⟨ρ, hβ, hβ1, hz⟩).elim

/-- The proposed intervention cannot supply an unconditional rejected family
without settling inhabitation of the original conditional zero domain. -/
private theorem zero_tail_law_iff : arena.Law zeroTail ↔
    ¬ ∃ ρ : ℂ, (1 / 2 : ℝ) < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 := by
  constructor
  · intro h ⟨ρ, hβ, hβ1, hz⟩
    have hh := h hβ hβ1 hz
    have hnρ : ρ ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
    have hna : ρ - 1 ≠ 0 := by
      intro he
      have hr := congrArg Complex.re (sub_eq_zero.mp he)
      simp only [one_re] at hr
      linarith
    have hA : (0 : ℝ) < (analyticOrderNatAt riemannZeta ρ : ℝ) / (‖ρ‖ * ‖ρ - 1‖) :=
      div_pos (by exact_mod_cast hh.1) (mul_pos (norm_pos_iff.mpr hnρ) (norm_pos_iff.mpr hna))
    obtain ⟨u, _, hu⟩ := hh.2.2 0 le_rfl hA 0
    simpa [zeroTail, realize] using hu
  · intro h ρ hβ hβ1 hz
    exact (h ⟨ρ, hβ, hβ1, hz⟩).elim

end Reg.D5.S3.Weil.Mertens.CriticalThetaTailPeak
