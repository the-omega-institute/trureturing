# Saturation and Strictness of the Landauer Bound

## Abstract

The exact Landauer slack separates equality from strictness through its two nonnegative remainders.

The frozen LandauerBound module obtains its inequality by discarding the nonnegative mutual-information and divergence remainders, but it does not say when equality holds. The slack identity below supplies exactly that missing information: the gap in the bound is the sum of the two discarded remainders. Every subsequent criterion is a consequence of this identity.

The conjunctive saturation criterion is the primary form. It identifies each discarded remainder separately, so saturation is read as no residual mutual information and no reservoir divergence, rather than merely as vanishing of their sum. The sum criterion is also stated and requires only the balance, without either nonnegativity hypothesis. Passing from a zero sum to the two separate zero statements is exactly where both nonnegativity hypotheses enter.

Under the same nonnegativity hypotheses as the frozen inequality, equality and strict inequality are exhaustive. The conjunctive theorem characterizes the equality case, while the final theorem characterizes the strict case by positivity of the total discarded remainder.

Physically, saturation is read here as no residual mutual information and no reservoir divergence. That reading is deliberately limited: this module proves only consequences of a real-number balance. It does not model a physical process, derive the balance from any dynamics, or establish that the variables named mutualInfo and divergence are the physical quantities their names suggest.

All four displays are authored legally because the current statement projector has no pinned projectable fixture for these declarations. Document construction therefore records a ProjectionGap for each theorem.

**Theorem 1.1 (The Landauer slack is the sum of the discarded remainders).**

$$\begin{gathered}\forall beta, heat, entropyChange, mutualInfo, divergence \in \mathbb{R},\\beta \cdot heat = -entropyChange + mutualInfo + divergence \Rightarrow\\beta \cdot heat - (-entropyChange) = mutualInfo + divergence.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/LandauerSaturation.landauer_slack_of_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rearranging the exact balance identifies the slack without an inequality or a sign assumption. Thus the quantity discarded in the frozen lower-bound argument is not merely bounded by the two remainders; it is exactly their sum.

**Theorem 1.2 (Saturation is equivalent to a zero remainder sum).**

$$\begin{gathered}\forall beta, heat, entropyChange, mutualInfo, divergence \in \mathbb{R},\\beta \cdot heat = -entropyChange + mutualInfo + divergence \Rightarrow\\-entropyChange = beta \cdot heat \Leftrightarrow mutualInfo + divergence = 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/LandauerSaturation.landauer_saturation_sum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The slack vanishes exactly when the sum of mutualInfo and divergence vanishes. Only the balance is used. Without nonnegativity, cancellation between the two real remainders is possible, so this algebraic criterion alone does not identify either remainder separately.

**Theorem 1.3 (Saturation means that both discarded remainders vanish).**

$$\begin{gathered}\forall beta, heat, entropyChange, mutualInfo, divergence \in \mathbb{R},\\beta \cdot heat = -entropyChange + mutualInfo + divergence \land 0 \le mutualInfo \land 0 \le divergence \Rightarrow\\-entropyChange = beta \cdot heat \Leftrightarrow (mutualInfo = 0 \land divergence = 0).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/LandauerSaturation.landauer_saturation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the primary saturation criterion. Nonnegativity prevents cancellation, so a zero total remainder is equivalent to mutualInfo being zero and divergence being zero. It therefore exposes the two independent equality conditions hidden by the frozen act of discarding their sum.

**Theorem 1.4 (Strictness is equivalent to a positive remainder sum).**

$$\begin{gathered}\forall beta, heat, entropyChange, mutualInfo, divergence \in \mathbb{R},\\beta \cdot heat = -entropyChange + mutualInfo + divergence \land 0 \le mutualInfo \land 0 \le divergence \Rightarrow\\-entropyChange < beta \cdot heat \Leftrightarrow 0 < mutualInfo + divergence.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/LandauerSaturation.landauer_strict_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the two nonnegativity hypotheses, the frozen lower bound rules out the opposite order. Its inequality is strict exactly when the exact slack is positive, equivalently when the sum of the discarded remainders is positive. Together with the preceding saturation criterion, this exhausts the bound's equality and strict cases.

## References

- Truth anchor: `D5/S3/DivergenceSupport/LandauerSaturation.landauer_saturation_iff`
- Truth anchor: `D5/S3/DivergenceSupport/LandauerSaturation.landauer_saturation_sum_iff`
- Truth anchor: `D5/S3/DivergenceSupport/LandauerSaturation.landauer_slack_of_balance`
- Truth anchor: `D5/S3/DivergenceSupport/LandauerSaturation.landauer_strict_iff`
- Dependency: [D5/S3/DivergenceSupport/LandauerBound](LandauerBound.md)
- Dependency: [D5/S3/DivergenceSupport/LandauerIdentity](LandauerIdentity.md)
