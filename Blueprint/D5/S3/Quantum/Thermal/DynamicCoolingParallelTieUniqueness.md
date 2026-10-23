# Strict global advantage over parallel dynamic cooling

## Abstract

For every initial excited population strictly between zero and one half, global unitary cooling gives a strictly smaller common target population than equal parallel single-target groups whenever M is at least two and N is at least M plus two, except for the pair (6, 2).

**Definition 1.1 (Single-qubit thermal weights).**

$$\forall P \in \mathbb{R},\; \forall b \in \operatorname{Fin}\left(2\right),\; \operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.tau}\left(P, b\right) = (\text{if} (b = 0) \text{then} 1 - P \text{else} P)$$

*Formalization.* `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.tau` (`✓ std3`).

*Citation.* Mattia Reda, Massimiliano Sacchi, Chiara Macchiavello, Giacomo Guarnieri (2026). *Optimal Dynamic Cooling of Multiple Qubits*. DOI: [10.48550/arXiv.2607.23641](https://doi.org/10.48550/arXiv.2607.23641). URL: <https://arxiv.org/abs/2607.23641v1>.

*Commentary.*

Equations (2) and (3) give the ground-state weight 1 minus P and the excited-state weight P. The definition is a real-valued function on Fin 2 for every real P; the thermal regime used below is 0 < P < 1/2.

**Definition 1.2 (The weight of a register string).**

$$\forall N \in \mathbb{N},\; \forall P \in \mathbb{R},\; \forall x \in (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)),\; \operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.thermalWeight}\left(P, x\right) = \prod_{j: \operatorname{Fin}\left(N\right)} \operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.tau}\left(P, x\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.thermalWeight` (`✓ std3`).

*Citation.* Mattia Reda, Massimiliano Sacchi, Chiara Macchiavello, Giacomo Guarnieri (2026). *Optimal Dynamic Cooling of Multiple Qubits*. DOI: [10.48550/arXiv.2607.23641](https://doi.org/10.48550/arXiv.2607.23641). URL: <https://arxiv.org/abs/2607.23641v1>.

*Commentary.*

Equations (2) through (4) describe N independent identical thermal qubits. A computational string is a function from Fin N to Fin 2, and its weight is the product of the single-qubit weights over all coordinates. The product also includes the empty register.

**Definition 1.3 (The diagonal thermal register state).**

$$\forall N \in \mathbb{N},\; \forall P \in \mathbb{R},\; \operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.rho}\left(N, P\right) = \operatorname{Matrix.diagonal}\left((\text{fun} x: (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \mapsto \operatorname{Complex.ofReal}\left(\operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.thermalWeight}\left(P, x\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.rho` (`✓ std3`).

*Citation.* Mattia Reda, Massimiliano Sacchi, Chiara Macchiavello, Giacomo Guarnieri (2026). *Optimal Dynamic Cooling of Multiple Qubits*. DOI: [10.48550/arXiv.2607.23641](https://doi.org/10.48550/arXiv.2607.23641). URL: <https://arxiv.org/abs/2607.23641v1>.

*Commentary.*

Equation (4) is the tensor power of the single-qubit state. In the computational basis it is Matrix.diagonal of the register weights, each embedded from the real numbers into the complex numbers.

**Definition 1.4 (The excited diagonal entry of a marginal).**

$$\forall N \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \forall alpha \in \operatorname{Fin}\left(N\right),\; \operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.population}\left(A, alpha\right) = \sum_{x: (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))} ((\text{if} (x\left(alpha\right) = 1) \text{then} A\left(x, x\right) \text{else} 0))$$

*Formalization.* `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.population` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mattia Reda, Massimiliano Sacchi, Chiara Macchiavello, Giacomo Guarnieri (2026). *Optimal Dynamic Cooling of Multiple Qubits*. DOI: [10.48550/arXiv.2607.23641](https://doi.org/10.48550/arXiv.2607.23641). URL: <https://arxiv.org/abs/2607.23641v1>.

*Commentary.*

For a complex matrix A and a coordinate alpha, sum its diagonal entries over all strings whose alpha coordinate is one. This is the excited diagonal entry of the one-qubit marginal. The definition applies to every matrix, without positivity or normalization assumptions.

**Definition 1.5 (The off-diagonal entry of a marginal).**

$$\forall N \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \forall alpha \in \operatorname{Fin}\left(N\right),\; \operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.coherence}\left(A, alpha\right) = \sum_{x: (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))} ((\text{if} (x\left(alpha\right) = 0) \text{then} A\left(x, \operatorname{Function.update}\left(x, alpha, 1\right)\right) \text{else} 0))$$

*Formalization.* `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.coherence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mattia Reda, Massimiliano Sacchi, Chiara Macchiavello, Giacomo Guarnieri (2026). *Optimal Dynamic Cooling of Multiple Qubits*. DOI: [10.48550/arXiv.2607.23641](https://doi.org/10.48550/arXiv.2607.23641). URL: <https://arxiv.org/abs/2607.23641v1>.

*Commentary.*

For each string whose alpha coordinate is zero, take the entry of A from that string to the string obtained by Function.update at alpha with value one. Their sum is the zero-one entry of the one-qubit marginal. This definition also applies to every complex matrix.

**Definition 1.6 (Common diagonal target marginals).**

$$\forall N \in \mathbb{N},\; \forall M \in \mathbb{N},\; \forall P \in \mathbb{R},\; \operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.feasible}\left(N, M, P\right) = \{g: \mathbb{R} \mid \exists U \in \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (U \in \operatorname{Matrix.unitaryGroup}\left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) \land (\forall alpha \in \operatorname{Fin}\left(N\right),\; (\operatorname{Fin.val}\left(alpha\right) < M) \Rightarrow ((\operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.population}\left(U \cdot \operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.rho}\left(N, P\right) \cdot \operatorname{star}\left(U\right), alpha\right) = \operatorname{Complex.ofReal}\left(g\right)) \land (\operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.coherence}\left(U \cdot \operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.rho}\left(N, P\right) \cdot \operatorname{star}\left(U\right), alpha\right) = 0)))\}$$

*Formalization.* `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.feasible` (`✓ std3`).

*Citation.* Mattia Reda, Massimiliano Sacchi, Chiara Macchiavello, Giacomo Guarnieri (2026). *Optimal Dynamic Cooling of Multiple Qubits*. DOI: [10.48550/arXiv.2607.23641](https://doi.org/10.48550/arXiv.2607.23641). URL: <https://arxiv.org/abs/2607.23641v1>.

*Commentary.*

Requirement 2 in Section I and the global optimization in Equation (90) ask for identical diagonal marginals on the first M coordinates. A real g belongs to this set when one unitary makes every coordinate alpha with Fin.val alpha < M have excited population g and coherence zero. The conjugated matrix has trace one and is Hermitian: the product weights sum to one and the initial matrix is real diagonal. Thus the other diagonal entry is 1 minus g and the other off-diagonal entry is the conjugate of zero. These two conditions say exactly that each target marginal is diag(1 minus g, g).

**Definition 1.7 (The optimal common target population).**

$$\forall N \in \mathbb{N},\; \forall M \in \mathbb{N},\; \forall P \in \mathbb{R},\; \operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.pGlob}\left(N, M, P\right) = \operatorname{sInf}\left(\operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.feasible}\left(N, M, P\right)\right)$$

*Formalization.* `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.pGlob` (`✓ std3`).

*Citation.* Mattia Reda, Massimiliano Sacchi, Chiara Macchiavello, Giacomo Guarnieri (2026). *Optimal Dynamic Cooling of Multiple Qubits*. DOI: [10.48550/arXiv.2607.23641](https://doi.org/10.48550/arXiv.2607.23641). URL: <https://arxiv.org/abs/2607.23641v1>.

*Commentary.*

Section I, requirement 2, and Equation (90) define the global optimum under equal diagonal target marginals. Here it is sInf in the real numbers of the set of feasible common populations. The definition is made for every N, M and P; the theorem uses parameters for which this set is nonempty and bounded below.

**Definition 1.8 (The strict global-versus-parallel inequality).**

$$(\operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.claim}) \Leftrightarrow (\forall N \in \mathbb{N},\; \forall M \in \mathbb{N},\; (2 \le M) \Rightarrow ((M + 2 \le N) \Rightarrow (((N, M) \ne (6, 2)) \Rightarrow (\forall P1 \in \mathbb{R},\; (0 < P1) \Rightarrow ((P1 < \frac{1}{2}) \Rightarrow (\operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.pGlob}\left(N, M, P1\right) < \operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.pGlob}\left(\operatorname{Nat.div}\left(N, M\right), 1, P1\right)))))))$$

*Formalization.* `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.claim` (`✓ std3`).

*Citation.* Mattia Reda, Massimiliano Sacchi, Chiara Macchiavello, Giacomo Guarnieri (2026). *Optimal Dynamic Cooling of Multiple Qubits*. DOI: [10.48550/arXiv.2607.23641](https://doi.org/10.48550/arXiv.2607.23641). URL: <https://arxiv.org/abs/2607.23641v1>.

*Commentary.*

Section IX, Equations (88) through (92), compares global cooling with M disjoint groups of size floor(N/M), each cooling one target, while leaving N modulo M qubits unused. The displayed Nat.div operator denotes natural-number integer division. The conjectured uniqueness of the exceptional tie gives the strict inequality for every natural pair with 2 <= M and M + 2 <= N other than (6, 2), and every real P1 with 0 < P1 < 1/2. The equality at (6, 2) is stated in Equation (92); it is not asserted by this claim.

**Theorem 1.9 (Global cooling strictly improves the parallel benchmark).**

$$\operatorname{D5.S3.Quantum.Thermal.DynamicCoolingParallelTieUniqueness.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.result` (`✓ std3`). ∎

*Resolves.* `Problems/reda-sacchi-macchiavello-guarnieri-2026-dynamic-cooling-tie-uniqueness` (proved) by `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"reda-sacchi-macchiavello-guarnieri-2026-dynamic-cooling-tie-uniqueness","declaration_gid":"D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mattia Reda, Massimiliano Sacchi, Chiara Macchiavello, Giacomo Guarnieri (2026). *Optimal Dynamic Cooling of Multiple Qubits*. DOI: [10.48550/arXiv.2607.23641](https://doi.org/10.48550/arXiv.2607.23641). URL: <https://arxiv.org/abs/2607.23641v1>.

*Commentary.*

For any unitary U, the squared moduli of its entries have row and column sums one. For an output set R, summing those squared moduli over R gives coefficients between zero and one whose total is the size of R. A threshold separating a set of that many smallest thermal weights from its complement therefore bounds the probability of R from below.

Let n be floor(N/M) and r be N modulo M. Among n-bit strings, the half-hot set consists of strings of weight greater than n/2 together with strings of weight exactly n/2 whose target bit is one. Complementing every bit pairs this set with its complement. Its thermal weights are at most the threshold P1 to the power ceil(n/2) times (1 minus P1) to the power n minus ceil(n/2), and the remaining weights are at least that threshold. The cutoff bound shows that its total weight is a lower bound for the optimal single-target population.

A cooling permutation in each of the M blocks sends the half-hot set to the target-excited half, so all targets initially reach that total weight. A real reflection then exchanges two orthogonal unit vectors: the equal superposition of M basis strings, each with exactly one target excited, and one basis string with every target in its ground state. The strings have total excitation counts k = ceil(n/2) and K = M floor(n/2) + r, respectively, and are fixed by the block permutation. The reflection reduces every target population by the same positive amount, the difference of their thermal weights divided by M, while every target coherence remains zero.

The arithmetic inequality ceil(n/2) < M floor(n/2) + (N modulo M) holds under the stated assumptions except at (N, M) = (6, 2). Since thermal weights strictly decrease with excitation count when 0 < P1 < 1/2, this gives a feasible common population strictly below the single-target lower bound. Taking the infimum over global unitaries proves the claim for every allowed pair and temperature.

## References

- Truth anchor: `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.claim`
- Truth anchor: `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.coherence`
- Truth anchor: `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.feasible`
- Truth anchor: `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.pGlob`
- Truth anchor: `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.population`
- Truth anchor: `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.result`
- Truth anchor: `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.rho`
- Truth anchor: `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.tau`
- Truth anchor: `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.thermalWeight`
- Dependency: [D5/S3/Entropy/NamingWindow/SumProductUpdate](../../Entropy/NamingWindow/SumProductUpdate.md)
- Dependency: [D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics](../Decoherence/ProjectedUnistochasticDynamics.md)
