# Two eigenvectors at eigenvalue -2

## Abstract

At L = 5, alpha = 1/3 and beta = 2/5, the annihilation-process generator has an eigenspace of dimension at least two at eigenvalue -2, refuting the Ayyer–Mallick maximal-degeneracy conjecture.

**Definition 1.1 (A bulk transition).**

$$\forall L \in \mathbb{N},\; \forall s \in \operatorname{Fin}\left(L\right) \to \operatorname{Bool},\; \forall i \in \operatorname{Fin}\left(L\right),\; \forall j \in \operatorname{Fin}\left(L\right),\; \operatorname{bulkMove}\left(s, i, j\right) = \operatorname{Function}.\operatorname{update}\left(\operatorname{Function}.\operatorname{update}\left(s, i, \operatorname{false}\right), j, \operatorname{Bool}.\operatorname{not}\left(s\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.bulkMove` (`✓ std3`).

*Citation.* A. Ayyer and K. Mallick (2010). *Exact results for an asymmetric annihilation process with open boundaries*. DOI: [10.1088/1751-8113/43/4/045003](https://doi.org/10.1088/1751-8113/43/4/045003). URL: <https://arxiv.org/abs/0910.0693>.

*Commentary.*

Ayyer–Mallick, Section II, p. 2, Eq. (1): "10 → 01 with rate 1," "11 → 00 with rate λ." At λ = 1, an occupied site is cleared and the next site is toggled. States are functions Fin L → Bool, with true denoting a particle; site 1 has index 0. The update expression also defines bulkMove when i and j coincide, although bulkCount uses only neighbouring distinct indices.

**Definition 1.2 (Counting bulk transitions).**

$$\forall L \in \mathbb{N},\; \forall s \in \operatorname{Fin}\left(L\right) \to \operatorname{Bool},\; \forall t \in \operatorname{Fin}\left(L\right) \to \operatorname{Bool},\; \operatorname{bulkCount}\left(L, s, t\right) = \sum_{i:\operatorname{Fin}\left(L\right)} (\operatorname{if} h:(\operatorname{val}\left(i\right) + 1 < L) \operatorname{then} \operatorname{if} ((s\left(i\right) = \operatorname{true}) \land (t = \operatorname{bulkMove}\left(s, i, \operatorname{Fin}.\operatorname{mk}\left(\operatorname{val}\left(i\right) + 1, h\right)\right))) \operatorname{then} 1 \operatorname{else} 0 \operatorname{else} 0)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.bulkCount` (`✓ std3`).

*Citation.* A. Ayyer and K. Mallick (2010). *Exact results for an asymmetric annihilation process with open boundaries*. DOI: [10.1088/1751-8113/43/4/045003](https://doi.org/10.1088/1751-8113/43/4/045003). URL: <https://arxiv.org/abs/0910.0693>.

*Commentary.*

Ayyer–Mallick, Section II, p. 2, Eq. (1): "10 → 01 with rate 1," "11 → 00 with rate λ." At λ = 1, bulkCount adds one for each occupied site i with a right neighbour whose bulkMove gives t. The positive branch constructs the Fin L index from val(i)+1 and its bound h. ite is if-then-else.

**Definition 1.3 (Counting the left boundary flip).**

$$\forall L \in \mathbb{N},\; \forall s \in \operatorname{Fin}\left(L\right) \to \operatorname{Bool},\; \forall t \in \operatorname{Fin}\left(L\right) \to \operatorname{Bool},\; \operatorname{leftCount}\left(L, s, t\right) = \operatorname{if} h:(0 < L) \operatorname{then} \operatorname{if} (t = \operatorname{Function}.\operatorname{update}\left(s, \operatorname{Fin}.\operatorname{mk}\left(0, h\right), \operatorname{Bool}.\operatorname{not}\left(s\left(\operatorname{Fin}.\operatorname{mk}\left(0, h\right)\right)\right)\right)) \operatorname{then} 1 \operatorname{else} 0 \operatorname{else} 0$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.leftCount` (`✓ std3`).

*Citation.* A. Ayyer and K. Mallick (2010). *Exact results for an asymmetric annihilation process with open boundaries*. DOI: [10.1088/1751-8113/43/4/045003](https://doi.org/10.1088/1751-8113/43/4/045003). URL: <https://arxiv.org/abs/0910.0693>.

*Commentary.*

Ayyer–Mallick, Section II, p. 2, Eq. (2): "0 → 1 with rate α," "1 → 0 with rate αλ." At λ = 1, both directions have rate α. When L is positive, leftCount is one precisely when flipping the first site gives t; otherwise it is zero.

**Definition 1.4 (Counting removal at the right boundary).**

$$\forall L \in \mathbb{N},\; \forall s \in \operatorname{Fin}\left(L\right) \to \operatorname{Bool},\; \forall t \in \operatorname{Fin}\left(L\right) \to \operatorname{Bool},\; \operatorname{rightCount}\left(L, s, t\right) = \operatorname{if} (0 < L) \operatorname{then} \operatorname{if} ((s\left(\langle \operatorname{Nat}.\operatorname{sub}\left(L, 1\right) \rangle\right) = \operatorname{true}) \land (t = \operatorname{Function}.\operatorname{update}\left(s, \langle \operatorname{Nat}.\operatorname{sub}\left(L, 1\right) \rangle, \operatorname{false}\right))) \operatorname{then} 1 \operatorname{else} 0 \operatorname{else} 0$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.rightCount` (`✓ std3`).

*Citation.* A. Ayyer and K. Mallick (2010). *Exact results for an asymmetric annihilation process with open boundaries*. DOI: [10.1088/1751-8113/43/4/045003](https://doi.org/10.1088/1751-8113/43/4/045003). URL: <https://arxiv.org/abs/0910.0693>.

*Commentary.*

Ayyer–Mallick, Section II, p. 2, Eq. (3): "1 → 0 with rate β." When L is positive, rightCount is one precisely when the last site is occupied and clearing it gives t. Nat.sub is truncated natural-number subtraction. The last-site Fin index is constructed with the bound inferred from 0 < L; the proof of that bound is omitted from the mathematical notation.

**Definition 1.5 (The total transition rate).**

$$\forall L \in \mathbb{N},\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \forall s \in \operatorname{Fin}\left(L\right) \to \operatorname{Bool},\; \forall t \in \operatorname{Fin}\left(L\right) \to \operatorname{Bool},\; \operatorname{offRate}\left(L, alpha, beta, s, t\right) = (\operatorname{Nat}.\operatorname{cast}\left(\operatorname{bulkCount}\left(L, s, t\right)\right):\mathbb{R}) + alpha \cdot (\operatorname{Nat}.\operatorname{cast}\left(\operatorname{leftCount}\left(L, s, t\right)\right):\mathbb{R}) + beta \cdot (\operatorname{Nat}.\operatorname{cast}\left(\operatorname{rightCount}\left(L, s, t\right)\right):\mathbb{R})$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.offRate` (`✓ std3`).

*Citation.* A. Ayyer and K. Mallick (2010). *Exact results for an asymmetric annihilation process with open boundaries*. DOI: [10.1088/1751-8113/43/4/045003](https://doi.org/10.1088/1751-8113/43/4/045003). URL: <https://arxiv.org/abs/0910.0693>.

*Commentary.*

Ayyer–Mallick, Section II, p. 2, Eqs. (1)–(3), at λ = 1: "10 → 01 with rate 1," "11 → 00 with rate λ," "0 → 1 with rate α," "1 → 0 with rate αλ," "1 → 0 with rate β." The rate is the sum of all bulk and boundary contributions. Counts are cast from natural numbers to real numbers before addition and multiplication.

**Definition 1.6 (The column-sum-zero generator).**

$$\forall L \in \mathbb{N},\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \forall t \in \operatorname{Fin}\left(L\right) \to \operatorname{Bool},\; \forall s \in \operatorname{Fin}\left(L\right) \to \operatorname{Bool},\; \operatorname{genMat}\left(L, alpha, beta\right)\left(t, s\right) = \operatorname{if} (t = s) \operatorname{then} -(\sum_{u:\operatorname{Fin}\left(L\right) \to \operatorname{Bool}} (\operatorname{if} (u \ne s) \operatorname{then} \operatorname{offRate}\left(L, alpha, beta, s, u\right) \operatorname{else} 0)) \operatorname{else} \operatorname{offRate}\left(L, alpha, beta, s, t\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.genMat` (`✓ std3`).

*Citation.* A. Ayyer and K. Mallick (2010). *Exact results for an asymmetric annihilation process with open boundaries*. DOI: [10.1088/1751-8113/43/4/045003](https://doi.org/10.1088/1751-8113/43/4/045003). URL: <https://arxiv.org/abs/0910.0693>.

*Commentary.*

Ayyer–Strehl, Definition 1, p. 463 (PDF p. 3): "A (continuous-time) transition matrix or Markov matrix or stochastic matrix is a square matrix of size equal to the cardinality of the configuration space whose (i, j)-th entry is given by the rate of the transition from configuration j to configuration i, when i is not equal to j. The (i, i)-th entry is then fixed by demanding that the entries in each column sum to zero." The column is the source state s and the row is the target state t. The diagonal is the negative sum of the rates to all other states.

**Definition 1.7 (The maximal-degeneracy assertion).**

$$claim \Leftrightarrow \left(\forall L \in \mathbb{N},\; (1 \le L) \Rightarrow (\forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; (0 < alpha) \Rightarrow ((0 < beta) \Rightarrow (\forall mu \in \mathbb{R},\; \operatorname{Module}.\operatorname{finrank}\left(\mathbb{R}, \operatorname{LinearMap}.\operatorname{ker}\left(\operatorname{Matrix}.\operatorname{toLin'}\left((\operatorname{genMat}\left(L, alpha, beta\right) - \operatorname{HSMul}.\operatorname{hSMul}\left(mu, 1\right))\right)\right)\right) \le 1)))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.claim` (`✓ std3`).

*Citation.* A. Ayyer and K. Mallick (2010). *Exact results for an asymmetric annihilation process with open boundaries*. DOI: [10.1088/1751-8113/43/4/045003](https://doi.org/10.1088/1751-8113/43/4/045003). URL: <https://arxiv.org/abs/0910.0693>.

*Commentary.*

Ayyer–Mallick, after Eq. (79), p. 14: "We also conjecture that the Markov matrices are maximally undiagonalizable in the sense that each eigenvalue seems to have exactly one eigenvector independent of the number of times the eigenvalue appears (this implies that the Jordan blocks are of the maximum possible size). In other words, the degeneracy seems to be so strong that the Markov matrix M_L which is of size 2^L has only 2L eigenvectors." Ayyer–Strehl, Conjecture 1, p. 466 (PDF p. 6): "The matrix M_L is maximally degenerate in the sense that it has exactly 2L eigenvectors." The claim is the geometric-multiplicity clause: every real eigenspace has dimension at most one for positive length and positive real rates. For numbers outside the spectrum the kernel has dimension zero. A real eigenvalue with a two-dimensional eigenspace also contradicts the unrestricted assertion.

**Theorem 1.8 (Refutation at length five).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ayyer-mallick-2010-annihilation-maximal-degeneracy` (refuted) by `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ayyer-mallick-2010-annihilation-maximal-degeneracy","declaration_gid":"D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Ayyer and K. Mallick (2010). *Exact results for an asymmetric annihilation process with open boundaries*. DOI: [10.1088/1751-8113/43/4/045003](https://doi.org/10.1088/1751-8113/43/4/045003). URL: <https://arxiv.org/abs/0910.0693>.

*Commentary.*

At L = 5, alpha = 1/3 and beta = 2/5, write p(n) for the product over indices i < n of -1 when s(i) is true and 1 otherwise. The integer-valued functions v1 = p(1)p(2) - 3p(2) + 9p(1) - 5 and v2 = p(1)p(4) - p(2)p(3) - 3p(4) + 9p(3) - 27p(2) + 81p(1) - 40 yield two real left eigenvectors at -2. Their values are (2,20) at the empty state and (2,24) at the state occupied only at index 3; the nonzero minor proves independence. Exact rational matrix-vector equalities transfer to the real generator by casting. Rank equality with the transpose and rank–nullity give dimension at least two for the right eigenspace, contradicting claim.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.bulkCount`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.bulkMove`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.genMat`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.leftCount`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.offRate`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/ParticleProcesses/AnnihilationMaximalDegeneracyRefutation.rightCount`
