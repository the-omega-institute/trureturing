# A counterexample to the Han–Wang–Yu spectral hull conjecture

## Abstract

Gluing two stochastic matrices yields an eigenvalue outside their spectral hull.

**Definition 1.1 (Finite chains with a selected root).**

$$\operatorname{structure} RootedChain \operatorname{where} \{n: \mathbb{N}; A: Matrix\left(Fin\left(n + 1\right), Fin\left(n + 1\right), \mathbb{R}\right); stochastic: A \in \operatorname{Matrix}.\operatorname{colStochastic}\left(\mathbb{R}, Fin\left(n + 1\right)\right)\}$$

*Formalization.* `D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.RootedChain` (`✓ std3`).

*Citation.* X. B. Han; S. Wang; C. Yu (2025). *PageRank of Gluing Networks and Corresponding Markov Chains*. DOI: [10.3390/math13132080](https://doi.org/10.3390/math13132080). URL: <https://www.mdpi.com/2227-7390/13/13/2080>.

*Commentary.*

Definition 8, page 10: "For integers i = 1, 2, ⋯, k, let M_i = (S_i, A_i) be k Markov chains, and v_0^i be a fixed point in S_i. Assume θ = (θ_1, θ_2, ⋯, θ_k), 0 < θ_i < 1, and Σ_{i=1}^k θ_i = 1." RootedChain has fields n, A and stochastic. Its states are Fin (n + 1), with selected root 0. The real matrix A is column stochastic: entry (v,w) is the transition probability from w to v. Source indices 1 through k become Fin k.

**Definition 1.2 (The transition matrix after gluing).**

$$\forall (k: \mathbb{N}), (\forall (M: (Fin\left(k\right)) \to (RootedChain)), (\forall (\theta: (Fin\left(k\right)) \to (\mathbb{R})), (\forall (x: Option\left(Sigma\left((\operatorname{fun} (i: Fin\left(k\right)) \mapsto Fin\left((M\left(i\right)).\operatorname{n}\right))\right)\right)), (\forall (y: Option\left(Sigma\left((\operatorname{fun} (i: Fin\left(k\right)) \mapsto Fin\left((M\left(i\right)).\operatorname{n}\right))\right)\right)), (glue\left(M, \theta, x, y\right) = \operatorname{match} x, y \operatorname{with} \begin{cases}none,none\mapsto \sum_{(i: Fin\left(k\right))} \theta\left(i\right) \cdot (M\left(i\right)).\operatorname{A}\left(0, 0\right)\\some\left(\langle i, v\rangle\right),none\mapsto \theta\left(i\right) \cdot (M\left(i\right)).\operatorname{A}\left((v).\operatorname{succ}, 0\right)\\none,some\left(\langle j, w\rangle\right)\mapsto (M\left(j\right)).\operatorname{A}\left(0, (w).\operatorname{succ}\right)\\some\left(\langle i, v\rangle\right),some\left(\langle j, w\rangle\right)\mapsto \operatorname{if} h: i = j \operatorname{then} (M\left(j\right)).\operatorname{A}\left((\operatorname{Eq}.\operatorname{rec}\left(v, h\right)).\operatorname{succ}, (w).\operatorname{succ}\right) \operatorname{else} 0\end{cases})))))$$

*Formalization.* `D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.glue` (`✓ std3`).

*Citation.* X. B. Han; S. Wang; C. Yu (2025). *PageRank of Gluing Networks and Corresponding Markov Chains*. DOI: [10.3390/math13132080](https://doi.org/10.3390/math13132080). URL: <https://www.mdpi.com/2227-7390/13/13/2080>.

*Commentary.*

Definition 8, page 10: "The θ-gluing of M_i along v_0^i is the following Markov chain M = (S, A)." The four cases give the source transition rule. The common root is none, and some ⟨i,v⟩ is state v.succ of input i. The transport h ▸ v changes the private index from chain i to chain j when h : i = j.

**Definition 1.3 (The proposed spectral containment).**

$$(claim) \Leftrightarrow (\forall (k: \mathbb{N}), (\forall (M: (Fin\left(k\right)) \to (RootedChain)), (\forall (\theta: (Fin\left(k\right)) \to (\mathbb{R})), ((\forall (i: Fin\left(k\right)), ((0 < \theta\left(i\right)) \land (\theta\left(i\right) < 1))) \Rightarrow ((\sum_{(i: Fin\left(k\right))} \theta\left(i\right) = 1) \Rightarrow (spectrum\left(\mathbb{C}, ((glue\left(M, \theta\right))).\operatorname{map}\left(algebraMap\left(\mathbb{R}, \mathbb{C}\right)\right)\right) \subseteq convexHull\left(\mathbb{R}, (\operatorname{Set}.\operatorname{iUnion} (\operatorname{fun} (i: Fin\left(k\right)) \mapsto spectrum\left(\mathbb{C}, (((M\left(i\right)).\operatorname{A})).\operatorname{map}\left(algebraMap\left(\mathbb{R}, \mathbb{C}\right)\right)\right)))\right)))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.claim` (`✓ std3`).

*Citation.* X. B. Han; S. Wang; C. Yu (2025). *PageRank of Gluing Networks and Corresponding Markov Chains*. DOI: [10.3390/math13132080](https://doi.org/10.3390/math13132080). URL: <https://www.mdpi.com/2227-7390/13/13/2080>.

*Commentary.*

Conjecture 1, §4.3, page 17: "Glue Markov chains M_i = (S_i, A_i) to a Markov chain M = (S, A), then all the eigenvalues of A lie in the convex hull of the eigenvalues of all A_i on the complex plane." The spectrum is taken over ℂ after applying algebraMap ℝ ℂ entrywise. The real convex hull lies in the complex plane. Every weight is strictly between zero and one and the weights sum to one.

**Theorem 1.4 (The spectral containment fails).**

$$\neg (\forall (k: \mathbb{N}), (\forall (M: (Fin\left(k\right)) \to (RootedChain)), (\forall (\theta: (Fin\left(k\right)) \to (\mathbb{R})), ((\forall (i: Fin\left(k\right)), ((0 < \theta\left(i\right)) \land (\theta\left(i\right) < 1))) \Rightarrow ((\sum_{(i: Fin\left(k\right))} \theta\left(i\right) = 1) \Rightarrow (spectrum\left(\mathbb{C}, ((glue\left(M, \theta\right))).\operatorname{map}\left(algebraMap\left(\mathbb{R}, \mathbb{C}\right)\right)\right) \subseteq convexHull\left(\mathbb{R}, (\operatorname{Set}.\operatorname{iUnion} (\operatorname{fun} (i: Fin\left(k\right)) \mapsto spectrum\left(\mathbb{C}, (((M\left(i\right)).\operatorname{A})).\operatorname{map}\left(algebraMap\left(\mathbb{R}, \mathbb{C}\right)\right)\right)))\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/han-wang-yu-gluing-spectrum` (refuted) by `D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"han-wang-yu-gluing-spectrum","declaration_gid":"D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* X. B. Han; S. Wang; C. Yu (2025). *PageRank of Gluing Networks and Corresponding Markov Chains*. DOI: [10.3390/math13132080](https://doi.org/10.3390/math13132080). URL: <https://www.mdpi.com/2227-7390/13/13/2080>.

*Commentary.*

Take two copies of B = (1/54)[[43,9,2],[2,36,16],[9,9,36]], rooted at 0, with weights (1/2,1/2). Every column sums to one and every entry is nonnegative. The characteristic polynomial is (μ−1)(μ−17/27)(μ−1/2), so every input spectral value has real part at least 1/2. The glued vector (0,−4,3,4,−3) has eigenvalue 4/9: the private blocks have opposite signs and their contributions to the root row cancel. Convexity of the half-plane Re z ≥ 1/2 excludes 4/9 from the input spectral hull.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.RootedChain`
- Truth anchor: `D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.glue`
- Truth anchor: `D5/S3/Quantum/Matrix/HanWangYuGluingSpectrumRefutation.result`
- Dependency: [D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree](../../Combinatorics/NonBacktracking/LaplacianGapMinDegree.md)
