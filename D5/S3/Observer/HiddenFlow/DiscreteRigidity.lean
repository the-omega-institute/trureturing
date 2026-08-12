/- GID: D5/S3/Observer/HiddenFlow/DiscreteRigidity
   generality: I
   mirror-B: D5/B/S3/Observer/HiddenFlow/DiscreteRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nonzero integer-parameter hidden actions admit no continuous real extension. -/

/- Library-search audit trail (2026-08-12):
   * `ContinuousAddMonoidHom.comp`, `Int.castAddHom`, and bundled-homomorphism extensionality
     provide the exact restriction interface from real parameters to integer parameters.
   * `AddSubgroup.cyclic_of_min` and `AddSubgroup.cyclic_of_isolated_zero` require an ordered
     Archimedean carrier and do not classify subgroups of the hidden p-adic product.
   * The frozen local theorem `continuous_hidden_flow_eq_zero` supplies the rigidity step, while
     `discreteHiddenJump_ne_zero` supplies the explicit anti-vacuity witness.
-/

import D5.S3.Observer.HiddenFlow.ContinuousRigidity

namespace D5.S3.Observer.HiddenFlow.DiscreteRigidity

open D5.S3.Observer.StreamlineTheorem
open D5.S3.Observer.HiddenFlow.ContinuousRigidity

/-- A nonzero integer-parameter action on hidden addresses cannot be the
restriction of a continuous additive real-parameter flow. This is a precise
integer-grading obstruction, not a classification of arbitrary actions. -/
theorem nonzero_integer_action_has_no_continuous_real_extension
    (jump : ℤ →+ HiddenAddress) (hjump : jump ≠ 0) :
    ¬ ∃ flow : ContinuousAddMonoidHom ℝ HiddenAddress,
      flow.toAddMonoidHom.comp (Int.castAddHom ℝ) = jump := by
  rintro ⟨flow, hflow⟩
  have hzero := continuous_hidden_flow_eq_zero flow
  subst flow
  apply hjump
  calc
    jump = (0 : ContinuousAddMonoidHom ℝ HiddenAddress).toAddMonoidHom.comp
        (Int.castAddHom ℝ) := hflow.symm
    _ = 0 := by
      apply AddMonoidHom.ext
      intro n
      rfl

/-- The canonical integer-cast jump is nonzero and, by continuous rigidity,
has no continuous additive real extension. Thus the positive integer action
and its forced separation from continuous real flows concern the same map. -/
theorem discrete_hidden_jump_is_nonzero_and_has_no_continuous_real_extension :
    discreteHiddenJump ≠ 0 ∧
      ¬ ∃ flow : ContinuousAddMonoidHom ℝ HiddenAddress,
        flow.toAddMonoidHom.comp (Int.castAddHom ℝ) = discreteHiddenJump :=
  ⟨discreteHiddenJump_ne_zero,
    nonzero_integer_action_has_no_continuous_real_extension
      discreteHiddenJump discreteHiddenJump_ne_zero⟩

end D5.S3.Observer.HiddenFlow.DiscreteRigidity
