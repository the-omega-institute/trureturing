# Survival Effects of a General Instrument Converge to the Largest Fixed Effect

## Abstract

The survival effects of a general no-click instrument decrease in the Loewner order to the largest effect fixed by the dual no-click map.

**Theorem 1.1 (Monotone limit and maximal fixed effect).**

$$\sum_{a \in \alpha} Q_{a}^{*} Q_{a} + \sum_{i \in \iota} L_{i}^{*} L_{i} = I \Rightarrow \exists F, S_{N} \to F,\\{}(\forall N, 0 \leq S_{N},\quad S_{N+1} \leq S_{N} \leq I,\quad F \leq S_{N}),\\{}0 \leq F \leq I,\quad \mathcal{A}(F) = F,\\{}\forall H, 0 \leq H \leq I \land \mathcal{A}(H) = H \Rightarrow H \leq F,\\{}\forall \rho, \operatorname{Tr}(\rho S_{N}) \to \operatorname{Tr}(\rho F).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/GeneralInstrumentSurvivalLimit.survival_tendsto_maximal_fixed_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha and iota be finite, let Q_a be the no-click and L_i the click Kraus operators on the d-dimensional space with the completeness relation, let A(X) be the sum of Q_a^* X Q_a over a, and let S_N = A^N(I). The order is the Loewner order: X <= Y means that Y - X is positive semidefinite.

The map A preserves positive semidefiniteness and hence the order, and S_0 - S_1 is the sum of L_i^* L_i, so the survival effects decrease and stay between 0 and I. For every vector the quadratic form of S_N is a bounded decreasing real sequence and converges; the polarization identity expresses every matrix entry through four quadratic forms, so S_N converges entrywise to a matrix F.

Positive semidefiniteness passes to limits, which gives 0 <= F <= S_N. Continuity of A and uniqueness of limits give A(F) = F. If 0 <= H <= I and A(H) = H, then H = A^N(H) <= A^N(I) = S_N for every N, and in the limit H <= F. The trace pairing with any rho is continuous, so Tr(rho S_N) converges to Tr(rho F).

## References

- Truth anchor: `D5/S3/Quantum/Measurement/GeneralInstrumentSurvivalLimit.survival_tendsto_maximal_fixed_effect`
- Dependency: [D5/S3/Quantum/Measurement/GeneralInstrumentDarkClosure](GeneralInstrumentDarkClosure.md)
