# An adaptive query advantage for four qubit states

## Abstract

Four qubit states admit an adaptive one-bit query with success 99/100, while every pre-measurement query has success at most 483/500.

Fin(n) consists of the indices 0 through n − 1. A one-bit query asks whether the state label belongs to a chosen finite subset X. Its two answers select X and its complement in Fin(n). The displayed conditional sets give these two subsets explicitly. Matrix.PosSemidef means positive semidefinite, Matrix.trace is the complex trace, and Complex.re takes its real part. The matrix 1 is the identity. Finset.Nonempty means that a finite set contains an element. All sums range over their displayed finite type or finite subset. The bracketed Fintype assumption is an anonymous instance supplying a finite enumeration.

**Definition 1.1 (Qubit matrices).**

$$\mathit{Q2} = \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(2\right), \operatorname{\mathit{Fin}}\left(2\right), \mathit{Complex}\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.Q2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hanwool Lee; Teiko Heinosaari (2026). *Perfect Discrimination of Non-Orthogonal Quantum States via Adaptive Post-Measurement Queries*. URL: <https://arxiv.org/abs/2608.01167v1>.

*Commentary.*

The qubit operators are complex matrices with two rows and two columns. Density matrices and measurement effects use this same matrix space.

**Definition 1.2 (Priors and density matrices).**

$$\forall n \in \mathit{Nat},\; \forall q \in \operatorname{\mathit{Fin}}\left(n\right) \to \mathit{Real},\; \forall R \in \operatorname{\mathit{Fin}}\left(n\right) \to \mathit{Q2},\; (\operatorname{\mathit{IsEnsemble}}\left(q, R\right)) \Leftrightarrow ((\forall x \in \operatorname{\mathit{Fin}}\left(n\right),\; 0 \le q\left(x\right)) \land ((\sum_{x:\operatorname{\mathit{Fin}}\left(n\right)}(q\left(x\right)) = 1) \land (\forall x \in \operatorname{\mathit{Fin}}\left(n\right),\; (\operatorname{\mathit{Matrix}}.\operatorname{\mathit{PosSemidef}}\left(R\left(x\right)\right)) \land (\operatorname{\mathit{Matrix}}.\operatorname{\mathit{trace}}\left(R\left(x\right)\right) = 1))))$$

*Formalization.* `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.IsEnsemble` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hanwool Lee; Teiko Heinosaari (2026). *Perfect Discrimination of Non-Orthogonal Quantum States via Adaptive Post-Measurement Queries*. URL: <https://arxiv.org/abs/2608.01167v1>.

*Commentary.*

An ensemble assigns a nonnegative prior to every label, with total prior one, and a positive semidefinite matrix of trace one to each label. This is the state-discrimination setting of equations (1) and (2), with arbitrary priors.

**Definition 1.3 (Finite quantum measurements).**

$$\forall iota \in \mathit{Type},\; [\operatorname{\mathit{Fintype}}\left(\mathit{iota}\right)], \forall M \in \mathit{iota} \to \mathit{Q2},\; (\operatorname{\mathit{IsPOVM}}\left(M\right)) \Leftrightarrow ((\forall z \in \mathit{iota},\; \operatorname{\mathit{Matrix}}.\operatorname{\mathit{PosSemidef}}\left(M\left(z\right)\right)) \land (\sum_{z:\mathit{iota}}(M\left(z\right)) = 1))$$

*Formalization.* `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.IsPOVM` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hanwool Lee; Teiko Heinosaari (2026). *Perfect Discrimination of Non-Orthogonal Quantum States via Adaptive Post-Measurement Queries*. URL: <https://arxiv.org/abs/2608.01167v1>.

*Commentary.*

A finite positive operator-valued measure consists of positive semidefinite effects summing to the identity. For a density matrix R and an effect E, Re tr(R E) is the probability of that measurement outcome, as in equation (1).

**Definition 1.4 (Querying before the measurement).**

$$\forall n \in \mathit{Nat},\; \forall X \in \operatorname{\mathit{Finset}}\left(\operatorname{\mathit{Fin}}\left(n\right)\right),\; \forall M \in \operatorname{\mathit{Fin}}\left(2\right) \to \left(\operatorname{\mathit{Fin}}\left(n\right) \to \mathit{Q2}\right),\; (\operatorname{\mathit{IsPreStrategy}}\left(X, M\right)) \Leftrightarrow (\forall ell \in \operatorname{\mathit{Fin}}\left(2\right),\; (\forall x \in \operatorname{\mathit{Fin}}\left(n\right),\; (x \in \operatorname{\mathit{if}} (\mathit{ell} = 0) \operatorname{\mathit{then}} X \operatorname{\mathit{else}} \operatorname{\mathit{Finset}}.\operatorname{\mathit{compl}}\left(X\right)) \Rightarrow (\operatorname{\mathit{Matrix}}.\operatorname{\mathit{PosSemidef}}\left(M\left(\mathit{ell}, x\right)\right))) \land ((\operatorname{\mathit{Finset}}.\operatorname{\mathit{Nonempty}}\left(\operatorname{\mathit{if}} (\mathit{ell} = 0) \operatorname{\mathit{then}} X \operatorname{\mathit{else}} \operatorname{\mathit{Finset}}.\operatorname{\mathit{compl}}\left(X\right)\right)) \Rightarrow (\sum_{x \in \operatorname{\mathit{if}} (\mathit{ell} = 0) \operatorname{\mathit{then}} X \operatorname{\mathit{else}} \operatorname{\mathit{Finset}}.\operatorname{\mathit{compl}}\left(X\right)}(M\left(\mathit{ell}, x\right)) = 1)))$$

*Formalization.* `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.IsPreStrategy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hanwool Lee; Teiko Heinosaari (2026). *Perfect Discrimination of Non-Orthogonal Quantum States via Adaptive Post-Measurement Queries*. URL: <https://arxiv.org/abs/2608.01167v1>.

*Commentary.*

The partition is chosen and its answer received before the measurement. For each nonempty answer subset, the receiver chooses a separate POVM indexed by that subset. Effects outside the corresponding subset are unrestricted and unused. An empty subset has no positivity or normalization requirements: its sum contributes zero. Thus X = Fin(n), whose other subset is empty, is included among the binary partitions in equation (3).

**Definition 1.5 (Success with a pre-measurement query).**

$$\forall n \in \mathit{Nat},\; \forall q \in \operatorname{\mathit{Fin}}\left(n\right) \to \mathit{Real},\; \forall R \in \operatorname{\mathit{Fin}}\left(n\right) \to \mathit{Q2},\; \forall X \in \operatorname{\mathit{Finset}}\left(\operatorname{\mathit{Fin}}\left(n\right)\right),\; \forall M \in \operatorname{\mathit{Fin}}\left(2\right) \to \left(\operatorname{\mathit{Fin}}\left(n\right) \to \mathit{Q2}\right),\; (\operatorname{\mathit{preValue}}\left(q, R, X, M\right):\mathit{Real}) = \sum_{\mathit{ell}:\operatorname{\mathit{Fin}}\left(2\right)}(\sum_{x \in \operatorname{\mathit{if}} (\mathit{ell} = 0) \operatorname{\mathit{then}} X \operatorname{\mathit{else}} \operatorname{\mathit{Finset}}.\operatorname{\mathit{compl}}\left(X\right)}(q\left(x\right) \cdot \operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{trace}}\left(R\left(x\right) \cdot M\left(\mathit{ell}, x\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.preValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hanwool Lee; Teiko Heinosaari (2026). *Perfect Discrimination of Non-Orthogonal Quantum States via Adaptive Post-Measurement Queries*. URL: <https://arxiv.org/abs/2608.01167v1>.

*Commentary.*

For a fixed partition and its two measurements, equation (3) sums the prior-weighted probabilities of correctly guessing each label. The two answer subsets are disjoint, so their contributions add. An empty subset contributes an empty sum, equal to zero. The expression is defined for arbitrary priors, matrices and effects; the preceding predicates specify when it describes a discrimination experiment.

**Definition 1.6 (The best pre-measurement value).**

$$\forall n \in \mathit{Nat},\; \forall q \in \operatorname{\mathit{Fin}}\left(n\right) \to \mathit{Real},\; \forall R \in \operatorname{\mathit{Fin}}\left(n\right) \to \mathit{Q2},\; (\operatorname{\mathit{Ppre}}\left(q, R\right):\mathit{Real}) = \operatorname{\mathit{sSup}}\left(\{v:\mathit{Real}|\exists X \in \operatorname{\mathit{Finset}}\left(\operatorname{\mathit{Fin}}\left(n\right)\right),\; \exists M \in \operatorname{\mathit{Fin}}\left(2\right) \to \left(\operatorname{\mathit{Fin}}\left(n\right) \to \mathit{Q2}\right),\; (\operatorname{\mathit{IsPreStrategy}}\left(X, M\right)) \land (v = \operatorname{\mathit{preValue}}\left(q, R, X, M\right))\}\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.Ppre` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hanwool Lee; Teiko Heinosaari (2026). *Perfect Discrimination of Non-Orthogonal Quantum States via Adaptive Post-Measurement Queries*. URL: <https://arxiv.org/abs/2608.01167v1>.

*Commentary.*

The real supremum ranges over the values of every partition X and every pair of measurements satisfying IsPreStrategy. This expresses the optimization in equation (3), including partitions with an empty subset. The definition itself imposes no ensemble hypothesis.

**Definition 1.7 (Queries chosen after an outcome).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall M \in \operatorname{\mathit{Fin}}\left(m\right) \to \mathit{Q2},\; \forall P \in \operatorname{\mathit{Fin}}\left(m\right) \to \operatorname{\mathit{Finset}}\left(\operatorname{\mathit{Fin}}\left(n\right)\right),\; \forall f \in \operatorname{\mathit{Fin}}\left(m\right) \to \left(\operatorname{\mathit{Fin}}\left(2\right) \to \operatorname{\mathit{Fin}}\left(n\right)\right),\; (\operatorname{\mathit{IsAdaptiveStrategy}}\left(M, P, f\right)) \Leftrightarrow ((\operatorname{\mathit{IsPOVM}}\left(M\right)) \land (\forall z \in \operatorname{\mathit{Fin}}\left(m\right),\; \forall ell \in \operatorname{\mathit{Fin}}\left(2\right),\; f\left(z, \mathit{ell}\right) \in \operatorname{\mathit{if}} (\mathit{ell} = 0) \operatorname{\mathit{then}} P\left(z\right) \operatorname{\mathit{else}} \operatorname{\mathit{Finset}}.\operatorname{\mathit{compl}}\left(P\left(z\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.IsAdaptiveStrategy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hanwool Lee; Teiko Heinosaari (2026). *Perfect Discrimination of Non-Orthogonal Quantum States via Adaptive Post-Measurement Queries*. URL: <https://arxiv.org/abs/2608.01167v1>.

*Commentary.*

The receiver first performs one finite POVM. After observing outcome z, the receiver chooses the subset P(z) and asks the one-bit query for that partition. For each possible answer, the guess must lie in the corresponding subset. Both the partition and the guesses may depend on z, as in equation (5). The two guesses therefore belong to different subsets.

**Definition 1.8 (Success with an adaptive post-measurement query).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall q \in \operatorname{\mathit{Fin}}\left(n\right) \to \mathit{Real},\; \forall R \in \operatorname{\mathit{Fin}}\left(n\right) \to \mathit{Q2},\; \forall M \in \operatorname{\mathit{Fin}}\left(m\right) \to \mathit{Q2},\; \forall f \in \operatorname{\mathit{Fin}}\left(m\right) \to \left(\operatorname{\mathit{Fin}}\left(2\right) \to \operatorname{\mathit{Fin}}\left(n\right)\right),\; (\operatorname{\mathit{adaptiveValue}}\left(q, R, M, f\right):\mathit{Real}) = \sum_{z:\operatorname{\mathit{Fin}}\left(m\right)}(\sum_{\mathit{ell}:\operatorname{\mathit{Fin}}\left(2\right)}(q\left(f\left(z, \mathit{ell}\right)\right) \cdot \operatorname{\mathit{Complex}}.\operatorname{\mathit{re}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{trace}}\left(R\left(f\left(z, \mathit{ell}\right)\right) \cdot M\left(z\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.adaptiveValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hanwool Lee; Teiko Heinosaari (2026). *Perfect Discrimination of Non-Orthogonal Quantum States via Adaptive Post-Measurement Queries*. URL: <https://arxiv.org/abs/2608.01167v1>.

*Commentary.*

Equation (5) adds the prior-weighted outcome probabilities for the two guesses at every measurement outcome. A label contributes when it equals the guess for the answer subset that contains it. The partition determines which guesses are allowed through IsAdaptiveStrategy; the numerical value depends only on the priors, states, measurement and guesses.

**Definition 1.9 (The proposed absence of advantage from four labels onward).**

$$(\mathit{claim}) \Leftrightarrow (\forall n \in \mathit{Nat},\; (4 \le n) \Rightarrow (\forall q \in \operatorname{\mathit{Fin}}\left(n\right) \to \mathit{Real},\; \forall R \in \operatorname{\mathit{Fin}}\left(n\right) \to \mathit{Q2},\; (\operatorname{\mathit{IsEnsemble}}\left(q, R\right)) \Rightarrow (\forall m \in \mathit{Nat},\; \forall M \in \operatorname{\mathit{Fin}}\left(m\right) \to \mathit{Q2},\; \forall P \in \operatorname{\mathit{Fin}}\left(m\right) \to \operatorname{\mathit{Finset}}\left(\operatorname{\mathit{Fin}}\left(n\right)\right),\; \forall f \in \operatorname{\mathit{Fin}}\left(m\right) \to \left(\operatorname{\mathit{Fin}}\left(2\right) \to \operatorname{\mathit{Fin}}\left(n\right)\right),\; (\operatorname{\mathit{IsAdaptiveStrategy}}\left(M, P, f\right)) \Rightarrow (\operatorname{\mathit{adaptiveValue}}\left(q, R, M, f\right) \le \operatorname{\mathit{Ppre}}\left(q, R\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.claim` (`✓ std3`).

*Citation.* Hanwool Lee; Teiko Heinosaari (2026). *Perfect Discrimination of Non-Orthogonal Quantum States via Adaptive Post-Measurement Queries*. URL: <https://arxiv.org/abs/2608.01167v1>.

*Commentary.*

Section VI suggests that an adaptive post-measurement query may never outperform a pre-measurement query for qubit ensembles with at least four labels. The statement quantifies over every such ensemble, every finite number of outcomes, and every adaptive strategy. It bounds each adaptive value by Ppre, expressing the suggested inequality without taking an additional supremum over adaptive strategies.

**Theorem 1.10 (Four pure states with a strict adaptive advantage).**

$$\neg (\mathit{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lee-heinosaari-2026-adaptive-query-four-qubit-states` (refuted) by `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lee-heinosaari-2026-adaptive-query-four-qubit-states","declaration_gid":"D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hanwool Lee; Teiko Heinosaari (2026). *Perfect Discrimination of Non-Orthogonal Quantum States via Adaptive Post-Measurement Queries*. URL: <https://arxiv.org/abs/2608.01167v1>.

*Commentary.*

Use labels 0, 1, 2, 3 with priors (33,33,33,1)/100. The four density matrices are [[1,0],[0,0]], (1/5)[[1,2],[2,4]], (1/5)[[1,−2],[−2,4]], and (1/2)[[1,1],[1,1]], respectively. Each is a rational positive semidefinite matrix of rank one and trace one, so all four states are pure.

Perform the three-outcome measurement with effects (3/4)[[0,0],[0,1]], (1/8)[[4,−2],[−2,1]], and (1/8)[[4,2],[2,1]]. These positive semidefinite matrices sum to the identity. Outcomes 0, 1, 2 have zero probability on states 0, 1, 2, respectively. At outcome 0, ask whether the label is in {1} and use guesses (1,2) for answers (0,1). At outcome 1, ask for {0} and use guesses (0,2). At outcome 2, ask for {0} and use guesses (0,1). The two surviving labels among 0, 1, 2 are distinguished at every outcome. Label 3 is never guessed. The success value is therefore 99/100.

For the pre-measurement upper bound, associate a rational symmetric matrix Y_C to each answer subset C, with Y_C − π_x R_x positive semidefinite for every x in C. Here π_x and R_x are the displayed prior and density matrix for label x. Write S(a,b,c) = [[a,b],[b,c]]. For each of the following eight subsets X, the ordered pair specifies (Y_X,Y_(X complement)); every binary partition occurs in this list up to exchanging its two subsets.

X = {0}: (S(33/100,0,0), S(99/500,0,99/250)). X = {0,1}: (S(173/500,33/500,7/25), S(147/2000,−16/125,533/2000)). X = {0,2}: (S(173/500,−33/500,7/25), S(27/400,33/250,529/2000)). X = {0,1,2}: (S(33/100,0,33/100), S(1/200,1/200,1/200)).

X = {0,3}: (S(661/2000,0,11/2000), S(99/500,0,99/250)). X = {0,1,3}: (S(173/500,33/500,7/25), S(33/500,−33/250,33/125)). X = {0,2,3}: (S(173/500,−33/500,7/25), S(33/500,33/250,33/125)). X = {0,1,2,3}: (S(33/100,0,33/100), S(0,0,0)).

The differences Y_C − π_x R_x have nonnegative diagonal entries and determinant. For a nonempty C and its POVM effects E_x, positivity gives π_x Re tr(R_x E_x) ≤ Re tr(Y_C E_x). Summing over C and using the identity sum of its effects bounds the contribution by Re tr(Y_C). An empty subset contributes zero, and all displayed traces are nonnegative. Each pair of traces has sum at most 483/500. The attainable pre-measurement value set is nonempty, so its supremum is at most 483/500. Since 99/100 exceeds 483/500 by 3/125, the four-state ensemble contradicts claim.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.IsAdaptiveStrategy`
- Truth anchor: `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.IsEnsemble`
- Truth anchor: `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.IsPOVM`
- Truth anchor: `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.IsPreStrategy`
- Truth anchor: `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.Ppre`
- Truth anchor: `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.Q2`
- Truth anchor: `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.adaptiveValue`
- Truth anchor: `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.preValue`
- Truth anchor: `D5/S3/Quantum/Measurement/AdaptiveQueryQubitFourStateRefutation.result`
- Dependency: [D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness](FreeSpectrahedronFeasibilityWitness.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
