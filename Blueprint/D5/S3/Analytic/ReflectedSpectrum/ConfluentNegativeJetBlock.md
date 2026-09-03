# Confluent Negative Jet Block

## Abstract

An invertible jet multiplier transports Hardy positivity to strict negativity and exact finite negative inertia.

**Theorem 1.1 (The confluent jet block is strictly negative).**

$$\forall m \in \operatorname{Nat}\left(\right), H \in \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \operatorname{Complex}\left(\right)\right), L \in \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \operatorname{Complex}\left(\right)\right), G \in \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \operatorname{Complex}\left(\right)\right),\; \left(\operatorname{PosDef}\left(H\right) \land \left(\operatorname{IsUnit}\left(L\right) \land \left(\operatorname{IsHermitian}\left(G\right) \land G = -{\operatorname{conjTranspose}\left(L\right) \times H \times L}\right)\right)\right) \Rightarrow \left(\operatorname{PosDef}\left(-G\right) \land \operatorname{negIndex}\left(G\right) = m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ConfluentNegativeJetBlock.confluent_negative_jet_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source's analytic zero cancellation and multiplication Leibniz rule are recorded as the factorization G equals minus L star H L. The Hardy derivative-evaluation Gram matrix H is positive definite, and the lower-triangular jet multiplier L is invertible.

Positive definiteness is preserved by invertible congruence. Hence minus G is positive definite, so G is strictly negative definite. All m eigenvalues are negative, giving exact negative index m and therefore the stated lower bound with equality.

**Theorem 1.2 (Exact inertia implies the source lower bound).**

$$\forall m \in \operatorname{Nat}\left(\right), H \in \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \operatorname{Complex}\left(\right)\right), L \in \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \operatorname{Complex}\left(\right)\right), G \in \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \operatorname{Complex}\left(\right)\right),\; \left(\operatorname{PosDef}\left(H\right) \land \left(\operatorname{IsUnit}\left(L\right) \land \left(\operatorname{IsHermitian}\left(G\right) \land G = -{\operatorname{conjTranspose}\left(L\right) \times H \times L}\right)\right)\right) \Rightarrow m \le \operatorname{negIndex}\left(G\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ReflectedSpectrum/ConfluentNegativeJetBlock.confluent_negative_jet_block_index_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the inequality-facing projection of the exact finite inertia theorem: the negative index is at least the jet order m.

## References

- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ConfluentNegativeJetBlock.confluent_negative_jet_block`
- Truth anchor: `D5/S3/Analytic/ReflectedSpectrum/ConfluentNegativeJetBlock.confluent_negative_jet_block_index_lower_bound`
- Dependency: [D5/S3/SpectralTopology/FiniteSpectralLocalizer](../../SpectralTopology/FiniteSpectralLocalizer.md)
