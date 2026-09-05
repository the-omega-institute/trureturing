# Countable Normal-Jet Criterion

## Abstract

Continuous normal-jet positivity is detected at rational ordinates.

**Theorem 1.1 (Continuous positivity is detected on the rationals).**

$$\forall f \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right),\; \operatorname{Continuous}\left(f\right) \Rightarrow \left(\left(\forall t \in \operatorname{Real}\left(\right),\; 0 \le f\left(t\right)\right) \Leftrightarrow \left(\forall q \in \operatorname{Rat}\left(\right),\; 0 \le f\left(q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CountableNormalJetCriterion.continuous_nonnegative_iff_rat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a continuous real-valued function, nonnegativity at every real point is equivalent to nonnegativity at every rational point. The reverse implication extends the closed nonnegative condition from the dense range of the rational embedding.

**Theorem 1.2 (Rational normal jets give a countable criterion and finite certificates).**

$$\left(\left(RH \Leftrightarrow \left(\forall t \in \operatorname{Real}\left(\right), m \in \operatorname{Nat}\left(\right),\; 0 \le \operatorname{normalJet}\left(t, m\right)\right)\right) \land \left(\forall m \in \operatorname{Nat}\left(\right),\; \operatorname{Continuous}\left((t \mapsto \operatorname{normalJet}\left(t, m\right))\right)\right)\right) \Rightarrow \left(\left(RH \Leftrightarrow \left(\forall q \in \operatorname{Rat}\left(\right), m \in \operatorname{Nat}\left(\right),\; 0 \le \operatorname{normalJet}\left(q, m\right)\right)\right) \land \left(\left(\neg RH\right) \Leftrightarrow \left(\exists q \in \operatorname{Rat}\left(\right), m \in \operatorname{Nat}\left(\right),\; \sum_{j=0}^{2m} \frac{(-1)^{m + j}}{\operatorname{factorial}\left(j\right) \cdot \operatorname{factorial}\left(2m - j\right)} \cdot \operatorname{iteratedDeriv}\left(j, criticalXi, q\right) \cdot \operatorname{iteratedDeriv}\left(2m - j, criticalXi, q\right) < 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CountableNormalJetCriterion.countable_normal_jet_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the analytic bridge identifying the Riemann hypothesis with nonnegativity of every real normal jet, and assume continuity in the ordinate at each depth. The dense rational criterion then gives the countable equivalence.

Negating that equivalence produces a rational ordinate q and a finite depth m with a negative jet. The imported normal-jet formula rewrites this witness as a finite signed factorial convolution of critical-xi derivatives from order zero through 2m.

The real-axis RH characterization is not available in D5 or pinned Mathlib and is deliberately exposed as a premise. The theorem proves the countable reduction and finite-certificate step; it does not claim to establish that missing analytic criterion.

## References

- Truth anchor: `D5/S3/Zeros/CountableNormalJetCriterion.continuous_nonnegative_iff_rat`
- Truth anchor: `D5/S3/Zeros/CountableNormalJetCriterion.countable_normal_jet_criterion`
- Dependency: [D5/S3/Zeros/NormalJetFormula](NormalJetFormula.md)
