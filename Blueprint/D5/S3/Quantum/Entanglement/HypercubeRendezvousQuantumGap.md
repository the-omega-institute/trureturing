# The quantum gap in hypercube rendezvous

## Abstract

For t ≥ 2 and d > 2t, the quantum supremum is strictly below the no-signalling supremum in balanced hypercube rendezvous.

**Definition 1.1 (Real correlation arrays).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{HypercubeRendezvousQuantumGap.Correlation}\left(d, t\right) = \left(\operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right) \to \left(\operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right) \to \left(\operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right) \to \left(\operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right) \to \mathbb{R}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.Correlation` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

The array assigns a real number to each ordered pair of inputs and outputs. Positivity, normalization and the choice of strategy class are imposed separately, as in §2.

**Definition 1.2 (Promised inputs).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall sigma \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall tau \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; (\operatorname{HypercubeRendezvousQuantumGap.Promised}\left(d, t, sigma, tau\right)) \Leftrightarrow (\operatorname{Finset.card}\left(\operatorname{symmDiff}\left(sigma, tau\right)\right) = 2 \cdot t)$$

*Formalization.* `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.Promised` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

The two starting vertices have Hamming distance 2t, the promise in §2.

**Definition 1.3 (The finite input set).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{HypercubeRendezvousQuantumGap.Inputs}\left(d, t\right) = \operatorname{Finset.filter}\left(\lambda (p: (\operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right) \times \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right))) \mapsto (\operatorname{HypercubeRendezvousQuantumGap.Promised}\left(d, t, \operatorname{Prod.fst}\left(p\right), \operatorname{Prod.snd}\left(p\right)\right)), (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right) \times \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right))\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.Inputs` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

Filter the set of all ordered vertex pairs by the distance promise. The value averages uniformly over this finite set, as in Eq. (2.7).

**Definition 1.4 (Average winning probability).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall P \in \operatorname{HypercubeRendezvousQuantumGap.Correlation}\left(d, t\right),\; \operatorname{HypercubeRendezvousQuantumGap.value}\left(P\right) = \frac{\sum_{p \in \operatorname{HypercubeRendezvousQuantumGap.Inputs}\left(d, t\right)} (\sum_{(A: \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right))} (\sum_{(B: \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right))} (\operatorname{ite}\left(\operatorname{RendezvousVectorSystemGap.Wins}\left(\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.snd}\left(p\right), A, B\right), P\left(\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.snd}\left(p\right), A, B\right), 0\right))))}{(\operatorname{Nat.cast}\left(\operatorname{Finset.card}\left(\operatorname{HypercubeRendezvousQuantumGap.Inputs}\left(d, t\right)\right)\right): \mathbb{R})}$$

*Formalization.* `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.value` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

Equation (2.7) sums the winning probabilities and divides by the number of promised ordered input pairs. The cardinality in the denominator is cast to the real numbers.

**Definition 1.5 (Finite-dimensional states and POVMs).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall alpha \in Type*,\; \forall beta \in Type*,\; \forall falpha \in \operatorname{Fintype}\left(alpha\right),\; \forall fbeta \in \operatorname{Fintype}\left(beta\right),\; \forall dalpha \in \operatorname{DecidableEq}\left(alpha\right),\; \forall dbeta \in \operatorname{DecidableEq}\left(beta\right),\; \operatorname{HypercubeRendezvousQuantumGap.QStrategy}\left(d, t, alpha, beta, falpha, fbeta, dalpha, dbeta\right) = \mathrm{structure} \{\rho: \operatorname{Matrix}\left((alpha \times beta), (alpha \times beta), \mathbb{C}\right); rho_{psd}: \operatorname{Matrix.PosSemidef}\left(\rho\right); rho_{trace}: \operatorname{Matrix.trace}\left(\rho\right) = (1: \mathbb{C}); E: \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right) \to \left(\operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right) \to \operatorname{Matrix}\left(alpha, alpha, \mathbb{C}\right)\right); F: \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right) \to \left(\operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right) \to \operatorname{Matrix}\left(beta, beta, \mathbb{C}\right)\right); E_{psd}: \forall sigma \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall A \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \operatorname{Matrix.PosSemidef}\left(E\left(sigma, A\right)\right); F_{psd}: \forall tau \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall B \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \operatorname{Matrix.PosSemidef}\left(F\left(tau, B\right)\right); E_{sum}: \forall sigma \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \sum_{(A: \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right))} (E\left(sigma, A\right)) = (1: \operatorname{Matrix}\left(alpha, alpha, \mathbb{C}\right)); F_{sum}: \forall tau \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \sum_{(B: \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right))} (F\left(tau, B\right)) = (1: \operatorname{Matrix}\left(beta, beta, \mathbb{C}\right))\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.QStrategy` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

A strategy consists of a positive semidefinite complex density matrix of trace one on the product of two finite index types, together with a POVM for each local input. Every effect is positive semidefinite, and each measurement sums to the identity. These are finite-dimensional quantum strategies in the sense of §2, Eq. (2.8). The local dimensions are arbitrary.

**Definition 1.6 (The Born correlation).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall alpha \in Type*,\; \forall beta \in Type*,\; \forall falpha \in \operatorname{Fintype}\left(alpha\right),\; \forall fbeta \in \operatorname{Fintype}\left(beta\right),\; \forall dalpha \in \operatorname{DecidableEq}\left(alpha\right),\; \forall dbeta \in \operatorname{DecidableEq}\left(beta\right),\; \forall S \in \operatorname{HypercubeRendezvousQuantumGap.QStrategy}\left(d, t, alpha, beta, falpha, fbeta, dalpha, dbeta\right),\; \forall sigma \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall tau \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall A \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \forall B \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \operatorname{HypercubeRendezvousQuantumGap.QStrategy.prob}\left(S, sigma, tau, A, B\right) = \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(S.\rho \cdot \operatorname{Matrix.kronecker}\left(S.E\left(sigma, A\right), S.F\left(tau, B\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.prob` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

For each input and output pair, take the real part of the trace of rho times the Kronecker product of the two POVM effects. This is the real-valued Born correlation used for the quantum strategies in §2.

**Definition 1.7 (Quantum realizability).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall P \in \operatorname{HypercubeRendezvousQuantumGap.Correlation}\left(d, t\right),\; (\operatorname{HypercubeRendezvousQuantumGap.IsQuantum}\left(P\right)) \Leftrightarrow (\exists alpha \in Type,\; \exists beta \in Type,\; \exists falpha \in \operatorname{Fintype}\left(alpha\right),\; \exists fbeta \in \operatorname{Fintype}\left(beta\right),\; \exists dalpha \in \operatorname{DecidableEq}\left(alpha\right),\; \exists dbeta \in \operatorname{DecidableEq}\left(beta\right),\; \exists S \in \operatorname{HypercubeRendezvousQuantumGap.QStrategy}\left(d, t, alpha, beta, falpha, fbeta, dalpha, dbeta\right),\; \operatorname{HypercubeRendezvousQuantumGap.QStrategy.prob}\left(S\right) = P)$$

*Formalization.* `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.IsQuantum` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

There exist two types in Type, finite enumerations and decidable equalities on those types, and a strategy with induced correlation equal to P. The existential instances are the instances used to form the strategy and its probability array.

**Definition 1.8 (No-signalling correlations).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall P \in \operatorname{HypercubeRendezvousQuantumGap.Correlation}\left(d, t\right),\; (\operatorname{HypercubeRendezvousQuantumGap.IsNS}\left(P\right)) \Leftrightarrow ((\forall sigma \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall tau \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall A \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \forall B \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; 0 \le P\left(sigma, tau, A, B\right)) \land ((\forall sigma \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall tau \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \sum_{(A: \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right))} (\sum_{(B: \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right))} (P\left(sigma, tau, A, B\right))) = 1) \land ((\forall sigma \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall tau \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall tauprime \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall A \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \sum_{(B: \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right))} (P\left(sigma, tau, A, B\right)) = \sum_{(B: \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right))} (P\left(sigma, tauprime, A, B\right))) \land (\forall sigma \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall sigmaprime \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall tau \in \operatorname{RendezvousVectorSystemGap.Vertex}\left(d\right),\; \forall B \in \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right),\; \sum_{(A: \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right))} (P\left(sigma, tau, A, B\right)) = \sum_{(A: \operatorname{RendezvousVectorSystemGap.Output}\left(d, t\right))} (P\left(sigmaprime, tau, A, B\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.IsNS` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

All entries are nonnegative, every input pair has total probability one, and each party's marginal is independent of the other party's input. These conditions apply to all input pairs, as in the no-signalling strategy class of §2.

**Definition 1.9 (Values of quantum correlations).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{HypercubeRendezvousQuantumGap.QValues}\left(d, t\right) = \{(r: \mathbb{R}) \mid \exists P \in \operatorname{HypercubeRendezvousQuantumGap.Correlation}\left(d, t\right),\; (\operatorname{HypercubeRendezvousQuantumGap.IsQuantum}\left(P\right)) \land (\operatorname{HypercubeRendezvousQuantumGap.value}\left(P\right) = r)\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.QValues` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

A real number belongs to this set precisely when it is the value of a finite-dimensional quantum correlation, as in Eq. (2.8).

**Definition 1.10 (Values of no-signalling correlations).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{HypercubeRendezvousQuantumGap.NSValues}\left(d, t\right) = \{(r: \mathbb{R}) \mid \exists P \in \operatorname{HypercubeRendezvousQuantumGap.Correlation}\left(d, t\right),\; (\operatorname{HypercubeRendezvousQuantumGap.IsNS}\left(P\right)) \land (\operatorname{HypercubeRendezvousQuantumGap.value}\left(P\right) = r)\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.NSValues` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

A real number belongs to this set precisely when it is the value of a no-signalling correlation, as in Eq. (2.8).

**Definition 1.11 (The quantum supremum).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{HypercubeRendezvousQuantumGap.omegaQ}\left(d, t\right) = \operatorname{sSup}\left(\operatorname{HypercubeRendezvousQuantumGap.QValues}\left(d, t\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.omegaQ` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

The quantum value is sSup of the set of quantum values. Equation (2.8) uses a supremum because finite-dimensional quantum correlations need not form a closed set.

**Definition 1.12 (The no-signalling supremum).**

$$\forall d \in \mathbb{N},\; \forall t \in \mathbb{N},\; \operatorname{HypercubeRendezvousQuantumGap.omegaNS}\left(d, t\right) = \operatorname{sSup}\left(\operatorname{HypercubeRendezvousQuantumGap.NSValues}\left(d, t\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.omegaNS` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

The no-signalling value is also expressed as sSup. Equation (2.8) expresses the optimum as a maximum; the formula here states the supremum definition used by the Lean module.

**Definition 1.13 (Wang's strict-gap question).**

$$(\operatorname{HypercubeRendezvousQuantumGap.claim}) \Leftrightarrow (\forall t \in \mathbb{N},\; \forall d \in \mathbb{N},\; (2 \le t) \Rightarrow ((2 \cdot t < d) \Rightarrow (\operatorname{HypercubeRendezvousQuantumGap.omegaQ}\left(d, t\right) < \operatorname{HypercubeRendezvousQuantumGap.omegaNS}\left(d, t\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.claim` (`✓ std3`).

*Citation.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

Section 7 asks whether the quantum value is strictly below the no-signalling value for t at least two and d greater than 2t. This proposition quantifies over exactly that range.

**Theorem 1.14 (The strict gap).**

$$\operatorname{HypercubeRendezvousQuantumGap.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.result` (`✓ std3`). ∎

*Resolves.* `Problems/wang-2026-hypercube-rendezvous-quantum-gap` (proved) by `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wang-2026-hypercube-rendezvous-quantum-gap","declaration_gid":"D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* C. Wang (2026). *Quantum-assisted rendezvous on hypercubes: a quantum Bernoulli noise approach*. URL: <https://arxiv.org/abs/2610.12949v1>.

*Commentary.*

The proposition holds. Averaging over translations and coordinate permutations gives a positive semidefinite vector system to which the quantitative vector bound applies. Every finite-dimensional quantum strategy has value at most (Nat.choose (2t) t / Nat.choose d t) times (1 − RendezvousVectorSystemGap.kappa d t), with the binomial coefficients cast to the real numbers. A no-signalling correlation attains the ratio of the two binomial coefficients. The positive factor kappa therefore separates the two suprema and answers the strict-gap question in Wang's §7.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.Correlation`
- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.Inputs`
- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.IsNS`
- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.IsQuantum`
- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.NSValues`
- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.Promised`
- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.QStrategy`
- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.QValues`
- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.omegaNS`
- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.omegaQ`
- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.prob`
- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.value`
- Dependency: [D5/S3/Quantum/Entanglement/RendezvousVectorSystemGap](RendezvousVectorSystemGap.md)
