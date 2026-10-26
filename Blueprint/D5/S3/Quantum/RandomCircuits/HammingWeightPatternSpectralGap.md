# The spectral gap of a connected Hamming-weight gate pattern

## Abstract

Connected patterns of polynomially many Hamming-weight-preserving gates have an inverse-polynomial spectral gap at fixed weight.

**Definition 1.1 (Exchanging two qubit labels).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(k: \mathbb{N}\right), \left(\forall \left(a: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(b: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(s: \operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right)\right), \left(\left(\operatorname{D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.swapConfig}\left(a, b, s\right): \operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right)\right) = \operatorname{Set.powersetCard.map}\left(k, \operatorname{Equiv.toEmbedding}\left(\operatorname{Equiv.swap}\left(a, b\right)\right), s\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.swapConfig` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Léo Monbroussou; Eliott Z. Mamon; Jonas Landman; Alex B. Grilo; Romain Kukla; Elham Kashefi (2025). *Trainability and Expressivity of Hamming-Weight Preserving Quantum Circuits for Machine Learning*. DOI: [10.22331/q-2025-05-15-1745](https://doi.org/10.22331/q-2025-05-15-1745). URL: <https://arxiv.org/abs/2309.15547v4>.

*Commentary.*

Choice n k is the type of k-element subsets of Fin n. Applying the transposition of a and b to every element of such a subset gives another subset of the same cardinality. A subset containing both labels or neither label is fixed. This construction expresses the exchange of the two qubit positions in the RBS/FBS gate descriptions, Quantum.tex lines 158–192.

**Definition 1.2 (A single stochastic gate).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(k: \mathbb{N}\right), \left(\forall \left(a: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(b: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(s: \operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right)\right), \left(\forall \left(t: \operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right)\right), \left(\left(\operatorname{D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.gateMatrix}\left(a, b, s, t\right): \mathbb{R}\right) = \operatorname{ite}\left(\left(s = t\right), \frac{\left(1: \mathbb{R}\right)}{\left(2: \mathbb{R}\right)}, \left(0: \mathbb{R}\right)\right) + \operatorname{ite}\left(\left(s = \operatorname{D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.swapConfig}\left(a, b, t\right)\right), \frac{\left(1: \mathbb{R}\right)}{\left(2: \mathbb{R}\right)}, \left(0: \mathbb{R}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.gateMatrix` (`✓ std3`).

*Citation.* Léo Monbroussou; Eliott Z. Mamon; Jonas Landman; Alex B. Grilo; Romain Kukla; Elham Kashefi (2025). *Trainability and Expressivity of Hamming-Weight Preserving Quantum Circuits for Machine Learning*. DOI: [10.22331/q-2025-05-15-1745](https://doi.org/10.22331/q-2025-05-15-1745). URL: <https://arxiv.org/abs/2309.15547v4>.

*Commentary.*

The real matrix has one half of the identity plus one half of the permutation matrix of the exchange. If the exchange fixes a configuration, its diagonal entry is one. Otherwise the two exchanged configurations each receive weight one half. These are the squared RBS/FBS entries at angle pi/4; the fermionic signs disappear on squaring. See Quantum.tex lines 158–192 and 1450–1458.

**Definition 1.3 (The ordered product of the gates).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(k: \mathbb{N}\right), \left(\forall \left(pat: \operatorname{List}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.patternMatrix}\left(pat\right): \operatorname{Matrix}\left(\operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right), \operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right), \mathbb{R}\right)\right) = \operatorname{List.prod}\left(\operatorname{List.reverse}\left(\operatorname{List.map}\left(\lambda \left(e: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right) \mapsto \left(\left(\operatorname{D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.gateMatrix}\left(\operatorname{Prod.fst}\left(e\right), \operatorname{Prod.snd}\left(e\right)\right): \operatorname{Matrix}\left(\operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right), \operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right), \mathbb{R}\right)\right)\right), pat\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.patternMatrix` (`✓ std3`).

*Citation.* Léo Monbroussou; Eliott Z. Mamon; Jonas Landman; Alex B. Grilo; Romain Kukla; Elham Kashefi (2025). *Trainability and Expressivity of Hamming-Weight Preserving Quantum Circuits for Machine Learning*. DOI: [10.22331/q-2025-05-15-1745](https://doi.org/10.22331/q-2025-05-15-1745). URL: <https://arxiv.org/abs/2309.15547v4>.

*Commentary.*

Map each ordered pair in pat to its gate matrix, reverse the list, and multiply. Thus the first gate in pat acts first on a column vector, and an empty pattern gives the identity matrix. The product order is T = T_J ... T_1 in Quantum.tex lines 1487–1489.

**Definition 1.4 (The graph of gate positions).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(pat: \operatorname{List}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.qubitGraph}\left(pat\right): \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)\right) = \operatorname{SimpleGraph.fromRel}\left(\lambda \left(x: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\lambda \left(y: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\left(x, y\right) \in pat\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.qubitGraph` (`✓ std3`).

*Citation.* Léo Monbroussou; Eliott Z. Mamon; Jonas Landman; Alex B. Grilo; Romain Kukla; Elham Kashefi (2025). *Trainability and Expressivity of Hamming-Weight Preserving Quantum Circuits for Machine Learning*. DOI: [10.22331/q-2025-05-15-1745](https://doi.org/10.22331/q-2025-05-15-1745). URL: <https://arxiv.org/abs/2309.15547v4>.

*Commentary.*

The vertices are the qubit labels. Distinct vertices x and y are adjacent when either ordered pair (x,y) or (y,x) occurs in pat. Repeated gates contribute the same edge, and diagonal pairs give no edge. This is the undirected form of the graph with arrows in both directions described in Quantum.tex lines 1631–1639.

**Definition 1.5 (Connected patterns).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(pat: \operatorname{List}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.connectedPattern}\left(pat\right)\right) \Leftrightarrow \left(\left(\forall \left(e: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right), \left(\left(e \in pat\right) \Rightarrow \left(\operatorname{Prod.fst}\left(e\right) \ne \operatorname{Prod.snd}\left(e\right)\right)\right)\right) \land \left(\operatorname{SimpleGraph.Connected}\left(\operatorname{D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.qubitGraph}\left(pat\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.connectedPattern` (`✓ std3`).

*Citation.* Léo Monbroussou; Eliott Z. Mamon; Jonas Landman; Alex B. Grilo; Romain Kukla; Elham Kashefi (2025). *Trainability and Expressivity of Hamming-Weight Preserving Quantum Circuits for Machine Learning*. DOI: [10.22331/q-2025-05-15-1745](https://doi.org/10.22331/q-2025-05-15-1745). URL: <https://arxiv.org/abs/2309.15547v4>.

*Commentary.*

Every gate has distinct endpoints, and the qubit graph is connected. Since each gate supplies both arrow directions, undirected connectivity is equivalent to the strong connectivity in the source's connected-pattern definition, Quantum.tex lines 1631–1640.

**Definition 1.6 (A uniform polynomial gap at fixed weight).**

$$\left(\operatorname{D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.claim}\right) \Leftrightarrow \left(\forall \left(k: \mathbb{N}\right), \left(\forall \left(c: \mathbb{N}\right), \left(\forall \left(a: \mathbb{N}\right), \left(\left(1 \le k\right) \Rightarrow \left(\forall \left(pat: \left(n: \mathbb{N}\right) \to \operatorname{List}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\left(\forall \left(n: \mathbb{N}\right), \left(\left(2 \le n\right) \Rightarrow \left(\left(\operatorname{D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.connectedPattern}\left(pat\left(n\right)\right)\right) \land \left(\operatorname{List.length}\left(pat\left(n\right)\right) \le c \cdot n^{a}\right)\right)\right)\right) \Rightarrow \left(\exists \left(d: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) < d\right) \land \left(\exists \left(b: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\left(k < n\right) \Rightarrow \left(\left(2 \le n\right) \Rightarrow \left(\forall \left(\mu: \mathbb{C}\right), \left(\forall \left(v: \left(\operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right)\right) \to \left(\mathbb{C}\right)\right), \left(\left(v \ne \operatorname{Function.const}\left(\operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right), \left(0: \mathbb{C}\right)\right)\right) \Rightarrow \left(\left(\sum_{s: \operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right)} \left(v\left(s\right)\right) = \left(0: \mathbb{C}\right)\right) \Rightarrow \left(\left(\operatorname{Matrix.mulVec}\left(\operatorname{Matrix.map}\left(\operatorname{D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.patternMatrix}\left(pat\left(n\right)\right), \lambda \left(x: \mathbb{R}\right) \mapsto \left(\operatorname{Complex.ofReal}\left(x\right)\right)\right), v\right) = \operatorname{HSMul.hSMul}\left(\mu, v\right)\right) \Rightarrow \left(\left\lVert \mu \right\rVert \le \left(1: \mathbb{R}\right) - \frac{d}{\left(\operatorname{Nat.cast}\left(n\right): \mathbb{R}\right)^{b}}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Léo Monbroussou; Eliott Z. Mamon; Jonas Landman; Alex B. Grilo; Romain Kukla; Elham Kashefi (2025). *Trainability and Expressivity of Hamming-Weight Preserving Quantum Circuits for Machine Learning*. DOI: [10.22331/q-2025-05-15-1745](https://doi.org/10.22331/q-2025-05-15-1745). URL: <https://arxiv.org/abs/2309.15547v4>.

*Commentary.*

Fix natural numbers k, c and a with k at least one. The family pat assigns an ordered gate list to every natural n. For every n at least two, assume that this list is connected and has length at most c times n to the power a. There must then be a positive real d and a natural b, uniform in n, such that every nonzero complex eigenvector with coordinate sum zero, at every n greater than k and at least two, has eigenvalue modulus at most 1 minus d divided by n to the power b. The real entries are included in the complex numbers before matrix-vector multiplication, and n is cast to a real number in the denominator. This is the sum-zero eigenvector formulation of the spectral-gap question in Quantum.tex lines 1977–1986; the source defines the gap as one minus the second-largest eigenvalue modulus in lines 1397–1405.

**Theorem 1.7 (An inverse-polynomial bound for every connected pattern family).**

$$\forall \left(k: \mathbb{N}\right), \left(\forall \left(c: \mathbb{N}\right), \left(\forall \left(a: \mathbb{N}\right), \left(\left(1 \le k\right) \Rightarrow \left(\forall \left(pat: \left(n: \mathbb{N}\right) \to \operatorname{List}\left(\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\left(\forall \left(n: \mathbb{N}\right), \left(\left(2 \le n\right) \Rightarrow \left(\left(\operatorname{D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.connectedPattern}\left(pat\left(n\right)\right)\right) \land \left(\operatorname{List.length}\left(pat\left(n\right)\right) \le c \cdot n^{a}\right)\right)\right)\right) \Rightarrow \left(\exists \left(d: \mathbb{R}\right), \left(\left(\left(0: \mathbb{R}\right) < d\right) \land \left(\exists \left(b: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\left(k < n\right) \Rightarrow \left(\left(2 \le n\right) \Rightarrow \left(\forall \left(\mu: \mathbb{C}\right), \left(\forall \left(v: \left(\operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right)\right) \to \left(\mathbb{C}\right)\right), \left(\left(v \ne \operatorname{Function.const}\left(\operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right), \left(0: \mathbb{C}\right)\right)\right) \Rightarrow \left(\left(\sum_{s: \operatorname{Erdos7.CommonTreeUnion.Choice}\left(n, k\right)} \left(v\left(s\right)\right) = \left(0: \mathbb{C}\right)\right) \Rightarrow \left(\left(\operatorname{Matrix.mulVec}\left(\operatorname{Matrix.map}\left(\operatorname{D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap.patternMatrix}\left(pat\left(n\right)\right), \lambda \left(x: \mathbb{R}\right) \mapsto \left(\operatorname{Complex.ofReal}\left(x\right)\right)\right), v\right) = \operatorname{HSMul.hSMul}\left(\mu, v\right)\right) \Rightarrow \left(\left\lVert \mu \right\rVert \le \left(1: \mathbb{R}\right) - \frac{d}{\left(\operatorname{Nat.cast}\left(n\right): \mathbb{R}\right)^{b}}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.result` (`✓ std3`). ∎

*Resolves.* `Problems/monbroussou-et-al-2025-hamming-weight-pattern-spectral-gap` (proved) by `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"monbroussou-et-al-2025-hamming-weight-pattern-spectral-gap","declaration_gid":"D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Léo Monbroussou; Eliott Z. Mamon; Jonas Landman; Alex B. Grilo; Romain Kukla; Elham Kashefi (2025). *Trainability and Expressivity of Hamming-Weight Preserving Quantum Circuits for Machine Learning*. DOI: [10.22331/q-2025-05-15-1745](https://doi.org/10.22331/q-2025-05-15-1745). URL: <https://arxiv.org/abs/2309.15547v4>.

*Commentary.*

First fix n and k and write X = Choice n k. Its cardinality is the binomial coefficient n choose k, which is at most n to the power k. For a gate exchanging a and b, let S act on complex functions on X by permuting their coordinates, and put P = (I + S)/2. The complexified gate matrix acts as P, and the complexified pattern matrix acts as the successive application of these operators in list order.

The coordinate permutation is an isometry, and w − Pw = (w − Sw)/2. The parallelogram identity gives ||Pw||² + ||w − Pw||² = ||w||². The residual formula and the triangle inequality show that ||w − Pw|| is at most ||w||. Linearity and this last bound imply ||w − Pw|| ≤ ||w − z|| + ||z − Pz|| for any w and z.

For the successive vectors w₀ = w and w_j = P_j w_{j−1}, put t_j = ||w_{j−1} − w_j||. There is one nonnegative t_j for each gate. Summing the preceding identity gives Σ_j t_j² = ||w||² − ||Tw||². Induction along the list, using the preceding inequality, bounds the defect ||w − P_j w|| of every gate at the initial vector by Σ_i t_i. Consequently E(w) = Σ_j ||w − P_j w||² is at most J(Σ_i t_i)², where J = (↑pat.length : ℝ) is the gate count cast to a real number. Cauchy–Schwarz gives (Σ_i t_i)² ≤ J Σ_i t_i², and hence E(w) ≤ J²(||w||² − ||Tw||²).

For each gate, expansion in coordinates gives ||w − Pw||² = (1/4)Σ_s |w(s) − w(swapConfig a b s)|². Now join distinct configurations whenever one gate exchange sends one to the other. To show that every pair is joined by a path, consider the qubit permutations whose action sends every configuration to a reachable configuration. They form a subgroup: reachability is reflexive, composes under permutation multiplication, and reverses to give inverses. This subgroup contains every gate transposition, including either orientation of every qubit edge. The edge transpositions of a connected qubit graph generate all permutations. Finally, two k-element subsets are related by a permutation, so any two configurations are reachable.

For a real function f on a finite graph, telescoping along a simple path and applying Cauchy–Schwarz bounds (f(x) − f(y))² by the path length times the sum of squared differences along that path. A simple path has length less than the number of vertices. Thus, writing N = (↑(Fintype.card X) : ℝ), (f(x) − f(y))² ≤ N A(f), where A(f) is the sum of (f(s) − f(t))² over ordered adjacent pairs.

Suppose Σ_s f(s) = 0. If X is empty, all the sums vanish. Otherwise choose vertices x and y where f is minimal and maximal. For every s, (f(s) − f(x))(f(y) − f(s)) ≥ 0. Summing and using the zero sum gives Σ_s f(s)² ≤ −N f(x)f(y). Since N(f(x) + f(y))² ≥ 0, it follows that 4Σ_s f(s)² ≤ N(f(x) − f(y))². Combining with the path bound yields 4Σ_s f(s)² ≤ N² A(f). Each configuration edge is supplied by a gate, so A(f) is at most the sum over all gates and configurations of the corresponding squared differences; repeated gates only increase that sum.

Apply the real inequality separately to the real and imaginary parts of a complex vector with coordinate sum zero. Adding them, using |z|² = (Re z)² + (Im z)² and the factor one quarter in the gate identity, gives ||w||² ≤ N² E(w). A connected pattern on at least two qubits has at least one gate: otherwise the qubit graph has no edges and cannot connect the distinct labels zero and one.

Identify a nonzero eigenvector v with w in the complex Euclidean space on X. Then Tw = μw, and ||w||² is positive. The existence of a nonzero coordinate also makes N positive. Combining the two energy bounds and cancelling ||w||² gives 1 ≤ J²N²(1 − |μ|²). Division by the positive J²N², followed by (|μ| − 1)² ≥ 0, yields |μ| ≤ 1 − 1/(2J²N²).

For the family in the statement, J ≤ (↑(max c 1) : ℝ)(↑n : ℝ)^a and N ≤ (↑n : ℝ)^k. Squaring these nonnegative bounds gives 2J²N² ≤ 2(↑(max c 1) : ℝ)²(↑n : ℝ)^(2a + 2k). Taking reciprocals of positive quantities gives the required estimate with d = 1/(2(↑(max c 1) : ℝ)²) > 0 and b = 2a + 2k. These choices depend only on k, c and a, so the same estimate holds for every n and every eigenvector specified in the statement.

## References

- Truth anchor: `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.claim`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.connectedPattern`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.gateMatrix`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.patternMatrix`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.qubitGraph`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.result`
- Truth anchor: `D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap.swapConfig`
- Dependency: [D5/S3/Arith/Congruence/ConditionalComparison/CommonTreeUnion](../../Arith/Congruence/ConditionalComparison/CommonTreeUnion.md)
- Dependency: [D5/S3/Zeros/EdgeTranspositionGeneration](../../Zeros/EdgeTranspositionGeneration.md)
