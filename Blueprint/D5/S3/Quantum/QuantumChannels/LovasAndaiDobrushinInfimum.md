# The least trace-distance contraction coefficient over a classical channel

## Abstract

A qubit channel lies over a classical channel when the images of the two basis projections have the prescribed diagonal entries. Over the classical channel with parameters a and f, the trace-distance contraction coefficient of every such qubit channel is at least |a - f|, and a measure-and-prepare channel attains this value.

**Definition 1.1 (Qubit channels over a classical channel).**

$$\forall a \in \mathbb{R},\; \forall f \in \mathbb{R},\; \operatorname{classicalFiber}\left(a, f\right) = \{Q \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right) \mid (((\operatorname{act}\left(Q, \operatorname{Matrix.single}\left(0, 0, 1\right)\right))\left(0, 0\right) = a) \land ((\operatorname{act}\left(Q, \operatorname{Matrix.single}\left(0, 0, 1\right)\right))\left(1, 1\right) = 1 - a)) \land (((\operatorname{act}\left(Q, \operatorname{Matrix.single}\left(1, 1, 1\right)\right))\left(0, 0\right) = f) \land ((\operatorname{act}\left(Q, \operatorname{Matrix.single}\left(1, 1, 1\right)\right))\left(1, 1\right) = 1 - f))\}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum.classicalFiber` (`✓ std3`).

*Citation.* Attila Lovas, Attila Andai (2016). *Volume of the space of qubit channels and some new results about the distribution of the quantum Dobrushin coefficient*. DOI: [10.48550/arXiv.1607.01215](https://doi.org/10.48550/arXiv.1607.01215). URL: <https://arxiv.org/abs/1607.01215>.

*Commentary.*

In the parametrization of Lovas and Andai the Choi blocks Q_11 and Q_22 are the images of the projections onto the first and the second basis vector, with diagonals (a, 1 - a) and (f, 1 - f). The set collects the completely positive trace-preserving qubit maps with these diagonal entries.

**Definition 1.2 (The trace-distance contraction coefficient).**

$$\forall Q \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right),\; \operatorname{dobrushin}\left(Q\right) = \operatorname{sSup}\left(\{x \in \mathbb{R} \mid \exists rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right),\; \exists sigma \in \operatorname{DensityState}\left(\operatorname{Fin}\left(2\right)\right),\; x = \frac{\operatorname{traceNorm}\left(\operatorname{Q.mapState}\left(rho\right) - \operatorname{Q.mapState}\left(sigma\right)\right)}{\operatorname{traceNorm}\left(rho - sigma\right)}\}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum.dobrushin` (`✓ std3`).

*Citation.* Attila Lovas, Attila Andai (2016). *Volume of the space of qubit channels and some new results about the distribution of the quantum Dobrushin coefficient*. DOI: [10.48550/arXiv.1607.01215](https://doi.org/10.48550/arXiv.1607.01215). URL: <https://arxiv.org/abs/1607.01215>.

*Commentary.*

The supremum, over all pairs of qubit states, of the ratio between the trace norm Tr|Q(rho) - Q(sigma)| of the difference of the images and the trace norm Tr|rho - sigma| of the difference of the states; a pair with rho = sigma contributes 0/0, which is 0 in Lean.

**Definition 1.3 (The Lovas-Andai conjecture).**

$$claim \Leftrightarrow (\forall a \in \mathbb{R},\; \forall f \in \mathbb{R},\; ((a \in [0, 1]) \land (f \in [0, 1])) \Rightarrow (\operatorname{IsLeast}\left(\operatorname{Set.image}\left(\operatorname{dobrushin}, \operatorname{classicalFiber}\left(a, f\right)\right), \left|a - f\right|\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum.claim` (`✓ std3`).

*Citation.* Attila Lovas, Attila Andai (2016). *Volume of the space of qubit channels and some new results about the distribution of the quantum Dobrushin coefficient*. DOI: [10.48550/arXiv.1607.01215](https://doi.org/10.48550/arXiv.1607.01215). URL: <https://arxiv.org/abs/1607.01215>.

*Commentary.*

For all parameters a and f in the unit interval, |a - f| is the least value of the contraction coefficient over the qubit channels above the classical channel; in particular the infimum equals |a - f| and is attained.

**Theorem 1.4 (The infimum is |a - f| and is attained).**

$$\forall a \in \mathbb{R},\; \forall f \in \mathbb{R},\; ((a \in [0, 1]) \land (f \in [0, 1])) \Rightarrow (\operatorname{IsLeast}\left(\operatorname{Set.image}\left(\operatorname{dobrushin}, \operatorname{classicalFiber}\left(a, f\right)\right), \left|a - f\right|\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/lovas-andai-2016-dobrushin-infimum` (proved) by `D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lovas-andai-2016-dobrushin-infimum","declaration_gid":"D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Attila Lovas, Attila Andai (2016). *Volume of the space of qubit channels and some new results about the distribution of the quantum Dobrushin coefficient*. DOI: [10.48550/arXiv.1607.01215](https://doi.org/10.48550/arXiv.1607.01215). URL: <https://arxiv.org/abs/1607.01215>.

*Commentary.*

Lower bound: for a channel Q over the classical channel, the images of the two basis projections differ by a matrix whose upper-left entry is a - f and, by trace preservation, whose lower-right entry is f - a. Testing the variational formula for the trace norm with the unitary diag(s, -s), where s is the sign of a - f, bounds that trace norm below by 2|a - f|, while the trace norm of the difference of the two projections is 2; so the ratio for this pair, and hence the coefficient, is at least |a - f|. Attainment: the measure-and-prepare channel with Kraus operators sqrt(p_j(i)) |i><j|, where p_0 = (a, 1 - a) and p_1 = (f, 1 - f), lies over the classical channel. It sends the difference of two states rho and sigma to the diagonal matrix with entries (a - f)t and (f - a)t, where t = rho_00 - sigma_00. Every unitary has diagonal entries of modulus at most one, so the variational formula bounds the trace norm of the image by 2|a - f||t|, while the same test unitary as before bounds the trace norm of rho - sigma below by 2|t|. Hence every ratio is at most |a - f|.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum.classicalFiber`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum.dobrushin`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/LovasAndaiDobrushinInfimum.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
