# Freeze-Deposit Trichotomy and Bounds

## Abstract

The freeze deposit obeys the complete critical inverse-temperature sign trichotomy.

The frozen module established only one branch: the freeze deposit is strictly positive exactly when beta exceeds the critical inverse temperature. The equality and negativity branches were absent. The first two results below supply those branches, so the three parallel criteria are exhaustive and the one-sided test becomes a sign trichotomy.

No combined trichotomy theorem is added. This is a deliberate decision rather than an omission: the three parallel criterion names already display the trichotomy, and a fourth declaration would merely restate proved content under a new name.

The two quantitative conclusions have different side hypotheses, and neither is decorative. Strict monotonicity requires a strictly positive entropy tax. With a zero tax the deposit is constant in beta, whereas with a negative tax it decreases. The upper bound requires only a nonnegative entropy tax together with positive beta; it does not require the tax to be strictly positive.

The upper bound is finite: the freeze deposit is at most the passive-energy shift. No limiting statement is claimed. In particular, this module does not prove that the deposit converges to the passive-energy shift as beta grows.

All four displays are authored legally because the current statement projector has no pinned projectable fixture for these declarations. Document construction therefore records a ProjectionGap for each theorem.

**Theorem 1.1 (The freeze deposit vanishes exactly at the critical inverse temperature).**

$$0<\beta \land 0<\Delta E_{pass} \Rightarrow (\operatorname{freezeDeposit}(\beta,\Delta S,\Delta E_{pass}) = 0 \Leftrightarrow \beta = \operatorname{criticalInverseTemperature}(\Delta S,\Delta E_{pass}))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FreezeTrichotomy.decoherence_freeze_eq_zero_iff_at_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive beta and a positive passive-energy shift, the deposit vanishes precisely when beta equals the entropy-tax to passive-energy ratio. The two positivity assumptions justify both divisions used to pass between the zero-deposit equation and the critical-temperature equation.

**Theorem 1.2 (The freeze deposit is negative exactly below the critical inverse temperature).**

$$0<\beta \land 0<\Delta E_{pass} \Rightarrow (\operatorname{freezeDeposit}(\beta,\Delta S,\Delta E_{pass}) < 0 \Leftrightarrow \beta < \operatorname{criticalInverseTemperature}(\Delta S,\Delta E_{pass}))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FreezeTrichotomy.decoherence_freeze_neg_iff_below_critical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same positivity assumptions, a negative deposit is equivalent to beta lying below the critical inverse temperature. Together with equality here and positivity in the frozen module, this completes the three possible signs without introducing a duplicate wrapper theorem.

**Theorem 1.3 (A positive entropy tax makes the freeze deposit strictly increase).**

$$0<\beta_{1} \land \beta_{1} < \beta_{2} \land 0<\Delta S \Rightarrow \operatorname{freezeDeposit}(\beta_{1},\Delta S,\Delta E_{pass}) < \operatorname{freezeDeposit}(\beta_{2},\Delta S,\Delta E_{pass})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FreezeTrichotomy.freeze_deposit_strictly_increases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If beta one is positive, beta two is larger, and the entropy tax is strictly positive, then the tax divided by beta strictly decreases. Subtracting that quantity from the same passive-energy shift makes the freeze deposit strictly increase. A zero or negative tax would invalidate this strict conclusion in exactly the ways stated above.

**Theorem 1.4 (The freeze deposit is bounded by the passive-energy shift).**

$$0<\beta \land 0\leq\Delta S \Rightarrow \operatorname{freezeDeposit}(\beta,\Delta S,\Delta E_{pass}) \leq \Delta E_{pass}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/FreezeTrichotomy.freeze_deposit_le_passive_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive beta, a nonnegative entropy tax yields a nonnegative scaled tax. Subtracting it from the passive-energy shift proves the finite upper bound. The theorem makes no assertion that this bound is approached or attained as beta tends toward any limit.

## References

- Truth anchor: `D5/S3/QuantumChannels/FreezeTrichotomy.decoherence_freeze_eq_zero_iff_at_critical`
- Truth anchor: `D5/S3/QuantumChannels/FreezeTrichotomy.decoherence_freeze_neg_iff_below_critical`
- Truth anchor: `D5/S3/QuantumChannels/FreezeTrichotomy.freeze_deposit_le_passive_energy`
- Truth anchor: `D5/S3/QuantumChannels/FreezeTrichotomy.freeze_deposit_strictly_increases`
- Dependency: [D5/S3/QuantumChannels/DecoherenceFreeze](DecoherenceFreeze.md)
