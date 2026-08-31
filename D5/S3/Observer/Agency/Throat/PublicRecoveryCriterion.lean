/- GID: D5/S3/Observer/Agency/Throat/PublicRecoveryCriterion
   generality: G
   mirror-B: D5/B/S3/Observer/Agency/Throat/PublicRecoveryCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Public recovery is equivalent to kernel containment and a zero covert throat. -/

import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Basic

/- Library-search audit trail (2026-09-01):
   * Repository searches found `target_recovery_criterion` for arbitrary
     function fibers, `payoff_price_factorization_iff` for scalar-valued linear
     maps, and `pair_readout_kernel_eq_intersection` for paired functions. None
     states the source's additive-group range factorization, covert-throat
     image criterion, and ledger monotonicity together.
   * Exact pinned-Mathlib hits `AddMonoidHom.liftOfRightInverse`,
     `AddMonoidHom.rangeRestrict_surjective`, `AddSubgroup.map_eq_bot_iff`, and
     `AddSubgroup.map_mono` supply the four standard steps below.
   * The ordered search stopped at these exact Mathlib components; no
     third-party dependency or parallel local reconstruction is needed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Agency.Throat.PublicRecoveryCriterion

/-- For additive-group transports, a hidden quantity is recoverable from the
public image exactly when every publicly silent control is hidden-silent,
equivalently when the image of the public kernel under the hidden transport is
zero. Adding a ledger replaces the public kernel by its intersection with the
ledger kernel, so its hidden image can only shrink.

The additive-group structure is the minimal explicit replacement for the
source's untyped uses of kernels, zero, kernel intersection, and kernel image. -/
theorem public_recovery_criterion
    {Control Public Hidden Ledger : Type*}
    [AddGroup Control] [AddGroup Public] [AddGroup Hidden] [AddGroup Ledger]
    (H : Control →+ Public) (K : Control →+ Hidden) (L : Control →+ Ledger) :
    ((∃ recover : H.range →+ Hidden, K = recover.comp H.rangeRestrict) ↔
        H.ker ≤ K.ker) ∧
      (H.ker ≤ K.ker ↔ H.ker.map K = ⊥) ∧
      (H.ker.map K = ⊥ ↔
        ∃ recover : H.range →+ Hidden, K = recover.comp H.rangeRestrict) ∧
      (H.ker ⊓ L.ker).map K ≤ H.ker.map K := by
  have factor_iff_kernel :
      (∃ recover : H.range →+ Hidden, K = recover.comp H.rangeRestrict) ↔
        H.ker ≤ K.ker := by
    constructor
    · rintro ⟨recover, factorization⟩
      intro control publicSilent
      rw [factorization]
      have rangeSilent : H.rangeRestrict control = 0 := by
        ext
        exact publicSilent
      simp [rangeSilent]
    · intro kernelInclusion
      let inverse : H.range → Control :=
        Function.surjInv H.rangeRestrict_surjective
      have rightInverse : Function.RightInverse inverse H.rangeRestrict :=
        Function.rightInverse_surjInv H.rangeRestrict_surjective
      have rangeKernel : H.rangeRestrict.ker ≤ K.ker := by
        simpa using kernelInclusion
      let bundled :
          {transport : Control →+ Hidden // H.rangeRestrict.ker ≤ transport.ker} :=
        ⟨K, rangeKernel⟩
      let recover : H.range →+ Hidden :=
        H.rangeRestrict.liftOfRightInverse inverse rightInverse bundled
      refine ⟨recover, ?_⟩
      exact (H.rangeRestrict.liftOfRightInverse_comp
        inverse rightInverse bundled).symm
  have kernel_iff_throat : H.ker ≤ K.ker ↔ H.ker.map K = ⊥ := by
    exact (AddSubgroup.map_eq_bot_iff H.ker (f := K)).symm
  refine ⟨factor_iff_kernel, kernel_iff_throat, ?_, ?_⟩
  · exact kernel_iff_throat.symm.trans factor_iff_kernel.symm
  · exact AddSubgroup.map_mono inf_le_left

#print axioms public_recovery_criterion

end D5.S3.Observer.Agency.Throat.PublicRecoveryCriterion
