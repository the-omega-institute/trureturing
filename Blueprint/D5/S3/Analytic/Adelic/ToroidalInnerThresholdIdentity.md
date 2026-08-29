# Toroidal Inner Threshold Identity

## Abstract

The common toroidal escape threshold equals the eventual-innerness threshold, and both vanish exactly on the completed-zeta critical line.

**Theorem 1.1 (Toroidal escape and eventual innerness have one critical width).**

$$\begin{gathered}\forall Index \in \operatorname{Type}\left(\right),\\P, T: Index \to \left(\operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right)\right),\\innerAt: \operatorname{Real}\left(\right) \to \operatorname{Prop}\left(\right),\\D := \left\{\exists s \in \operatorname{Complex}\left(\right),\; \frac{1}{2} \leq \operatorname{re}\left(s\right) \land \left(\left(\forall i \in Index,\; P\left(i\right)\left(s\right) = 0\right) \land d = \operatorname{re}\left(s\right) - \frac{1}{2}\right) \mid d \in \operatorname{Real}\left(\right)\right\},\\omegaTor := \operatorname{sSup}\left(D\right),\\A := \left\{0 \leq a \land \left(\forall omega \in \operatorname{Real}\left(\right),\; a < omega \Rightarrow innerAt\left(omega\right)\right) \mid a \in \operatorname{Real}\left(\right)\right\},\\omegaIn := \operatorname{sInf}\left(A\right),\\criticalLine := \forall s \in \operatorname{Complex}\left(\right),\; xiReading\left(s\right) = 0 \Rightarrow \operatorname{re}\left(s\right) = \frac{1}{2},\\(\left(\forall i \in Index, s \in \operatorname{Complex}\left(\right),\; P\left(i\right)\left(s\right) = xiReading\left(s\right) \times T\left(i\right)\left(s\right)\right) \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; \exists i \in Index,\; T\left(i\right)\left(s\right) \neq 0\right) \land \left(\left(\forall a \in \operatorname{Real}\left(\right),\; 0 \leq a \Rightarrow \left(\left(\forall omega \in \operatorname{Real}\left(\right),\; a < omega \Rightarrow innerAt\left(omega\right)\right) \Leftrightarrow \left(\forall s \in \operatorname{Complex}\left(\right),\; xiReading\left(s\right) = 0 \Rightarrow \operatorname{re}\left(s\right) \leq \frac{1}{2} + a\right)\right)\right) \land \left(\operatorname{Nonempty}\left(D\right) \land \operatorname{BddAbove}\left(D\right)\right)\right)\right)) \Rightarrow\\omegaTor = omegaIn \land \left(\left(criticalLine \Leftrightarrow omegaTor = 0\right) \land \left(criticalLine \Leftrightarrow omegaIn = 0\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Adelic/ToroidalInnerThresholdIdentity.toroidal_inner_threshold_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The deviation set is constructed from right-half-plane spectral points invisible to every supplied period readout. Its supremum is the toroidal threshold. The inner candidate set is constructed from nonnegative widths beyond which every larger width is inner; its infimum is the inner threshold.

Pointwise twist nonvanishing and the displayed factorization identify common period zeros with xiReading zeros. The Suzuki equivalence then identifies inner candidates with upper bounds of the deviation set, so the conditional-completeness infimum/supremum theorem gives the threshold equality.

Nonemptiness and boundedness are explicit because real sSup and sInf are conditional. Reflection of xiReading turns the right-half threshold criterion into the displayed global critical-line predicate.

## References

- Truth anchor: `D5/S3/Analytic/Adelic/ToroidalInnerThresholdIdentity.toroidal_inner_threshold_identity`
- Dependency: [D5/S3/Analytic/Adelic/ToroidalCommonZeroLocus](ToroidalCommonZeroLocus.md)
