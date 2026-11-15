import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.ThetaTailExtremumTransfer
import Reg.Support.DependentFamily

/-! The full conditional source law, with its two arithmetic readout occurrences,
and the actual signed-tail existence required by whole-family variation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.ThetaTailExtremumTransfer
open _root_.D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope (B)
open _root_.D5.S3.Weil.Mertens.ActualThetaTailLaplace (F)

namespace Reg.D5.S3.Arith.Robin.Analytic.ThetaTailExtremumTransfer

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => B x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {b cplus cminus : ℝ}, 0 < b → b < 1 →
    0 < cplus → 0 < cminus →
    (∀ T : ℝ, ∃ x : ℝ, max T 2 < x ∧ cplus * Real.rpow x (-b) ≤ -F x) →
    (∀ T : ℝ, ∃ x : ℝ, max T 2 < x ∧ -F x ≤ -cminus * Real.rpow x (-b)) →
    (∀ T : ℝ, ∃ x : ℝ, max T 2 < x ∧
      (cplus / 4) * Real.rpow x (-b) ≤ V.readout true () x) ∧
    (∀ T : ℝ, ∃ x : ℝ, max T 2 < x ∧
      V.readout false () x ≤ -(cminus / 2) * Real.rpow x (-b))

private theorem actual_law : arena.Law actual := @actual_theta_tail_omega_pm_to_B

private theorem source_bridge :
    (type_of% (@actual_theta_tail_omega_pm_to_B)) ↔ arena.Law actual := Iff.rfl

private def TwoSignedActualTail : Prop :=
  ∃ b cplus cminus : ℝ, 0 < b ∧ b < 1 ∧ 0 < cplus ∧ 0 < cminus ∧
    (∀ T : ℝ, ∃ x : ℝ, max T 2 < x ∧ cplus * Real.rpow x (-b) ≤ -F x) ∧
    (∀ T : ℝ, ∃ x : ℝ, max T 2 < x ∧ -F x ≤ -cminus * Real.rpow x (-b))

private theorem law_of_no_two_signed_actual_tail (h : ¬ TwoSignedActualTail)
    (V : Realization signature) : arena.Law V := by
  intro b cp cm hb hb1 hcp hcm hp hm
  exact (h ⟨b, cp, cm, hb, hb1, hcp, hcm, hp, hm⟩).elim

private theorem rejected_family_requires_two_signed_actual_tail
    {V : Realization signature} (h : ¬ arena.Law V) : TwoSignedActualTail := by
  by_contra hn
  exact h (law_of_no_two_signed_actual_tail hn V)

private theorem variation_requires_two_signed_actual_tail
    (h : Variation arena actual) : TwoSignedActualTail := by
  obtain ⟨V, hV⟩ := h.2
  exact rejected_family_requires_two_signed_actual_tail hV

/- A faithful four-slot audit is unfinished. The complete law fixes the actual
tail F in both hypotheses and varies the two conclusion occurrences of B.
Any rejected whole family therefore proves TwoSignedActualTail. The public
critical_theta_tail_peak supplies only the negative K=-F sign, leaving the
positive actual power-scale sign unproved. No variation, sensitivity, actual
observational dependence, or Contract.Registration is asserted here. -/

end Reg.D5.S3.Arith.Robin.Analytic.ThetaTailExtremumTransfer
