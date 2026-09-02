# Projective Toroidal Jet Scale Invariance

## Abstract

A nonzero constant rescaling preserves the normalized projective toroidal jet fingerprint.

**Theorem 1.1 (Common nonzero scale leaves the fingerprint unchanged).**

$$\forall period \in \operatorname{Complex}\left(\right) \to \operatorname{Complex}\left(\right), s \in \operatorname{Complex}\left(\right), c \in \operatorname{Complex}\left(\right), m \in \operatorname{Nat}\left(\right), r \in \operatorname{Nat}\left(\right),\; \left(c \ne 0 \land \left(\left(\forall j \in \operatorname{Nat}\left(\right),\; j < m \Rightarrow \operatorname{iteratedDeriv}\left(j, period, s\right) = 0\right) \land \operatorname{iteratedDeriv}\left(m, period, s\right) \ne 0\right)\right) \Rightarrow \operatorname{projectiveToroidalJet}\left(period, s, m, r\right) = \operatorname{projectiveToroidalJet}\left((z: \operatorname{Complex}\left(\right) \mapsto c \times period\left(z\right)), s, m, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Toroidal/ProjectiveJetScaleInvariance.projective_toroidal_jet_scale_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fingerprint records the supplied anchor order m and the next r iterated derivatives divided by the nonzero derivative at m. This invariance theorem is the named property that earns the fingerprint and normalized-jet definitions.

Multiplication by a nonzero constant preserves every earlier zero and the nonzero anchor. The same constant then cancels from every normalized derivative ratio.

The anchor order is supplied by the displayed hypotheses. ToroidalJetDepth may produce such an order for a later consumer, but it is not a dependency here. No zeta, Riemann-hypothesis, or C-1 chart statement is asserted.

## References

- Truth anchor: `D5/S3/Analytic/Toroidal/ProjectiveJetScaleInvariance.projective_toroidal_jet_scale_invariance`
