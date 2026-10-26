# Minimum Seidel energy of chain graphs

## Abstract

Every connected chain graph has at least the Seidel energy of each member of Gamma(n,k), with equality precisely for the members of that family.

**Definition 1.1 (Characteristic-root energy).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall (M : \operatorname{Matrix}\left(V, V, \mathbb{R}\right)), \operatorname{energy}\left(M\right) = \operatorname{Multiset.sum}\left(\operatorname{Multiset.map}\left(\operatorname{fun} (x : \mathbb{R}) \mapsto \lvert x\rvert, \operatorname{Polynomial.roots}\left(\operatorname{Matrix.charpoly}\left(M\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.energy` (`✓ std3`).

*Citation.* Santanu Mandal, Ranjit Mehatari, and Kinkar Chandra Das (2022). *On the spectrum and energy of Seidel matrix for chain graphs*. DOI: [10.48550/arXiv.2205.00310](https://doi.org/10.48550/arXiv.2205.00310). URL: <https://arxiv.org/abs/2205.00310v1>.

*Commentary.*

Page 2: "The Seidel energy SE(G) of a graph G is defined as the sum of absolute values of the eigenvalues of Seidel matrix S." The expression uses real characteristic roots with multiplicity. Its applications here are real symmetric matrices.

**Theorem 1.2 (Energy in an eigenbasis).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall (X : \operatorname{Matrix}\left(V, V, \mathbb{R}\right)), \forall (hX : \operatorname{Matrix.IsHermitian}\left(X\right)), \operatorname{energy}\left(X\right) = \operatorname{Finset.sum}\left(\operatorname{Finset.univ}, \operatorname{fun} (i : V) \mapsto \lvert \operatorname{Matrix.IsHermitian.eigenvalues}\left(hX, i\right)\rvert\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.energy_eigenvalues` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Santanu Mandal, Ranjit Mehatari, and Kinkar Chandra Das (2022). *On the spectrum and energy of Seidel matrix for chain graphs*. DOI: [10.48550/arXiv.2205.00310](https://doi.org/10.48550/arXiv.2205.00310). URL: <https://arxiv.org/abs/2205.00310v1>.

*Commentary.*

For a real symmetric matrix, the real roots of the characteristic polynomial are precisely its eigenvalues with multiplicity.

**Theorem 1.3 (Trace of the positive square root).**

$$\forall (V : Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall (X : \operatorname{Matrix}\left(V, V, \mathbb{R}\right)), \forall (hX : \operatorname{Matrix.IsHermitian}\left(X\right)), \operatorname{Finset.sum}\left(\operatorname{Finset.univ}, \operatorname{fun} (i : V) \mapsto \lvert \operatorname{Matrix.IsHermitian.eigenvalues}\left(hX, i\right)\rvert\right) = \operatorname{Matrix.trace}\left(\operatorname{CFC.sqrt}\left(\operatorname{Matrix.transpose}\left(X\right) \cdot X\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.sum_abs_eq_trace_sqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Santanu Mandal, Ranjit Mehatari, and Kinkar Chandra Das (2022). *On the spectrum and energy of Seidel matrix for chain graphs*. DOI: [10.48550/arXiv.2205.00310](https://doi.org/10.48550/arXiv.2205.00310). URL: <https://arxiv.org/abs/2205.00310v1>.

*Commentary.*

The positive square root of the transpose product has absolute eigenvalues. Its trace is their sum.

**Definition 1.4 (The alternating binary string).**

$$\forall (k : \mathbb{N}), \forall (s : \operatorname{Fin}\left(k\right) \to \mathbb{N}), \forall (t : \operatorname{Fin}\left(k\right) \to \mathbb{N}), \operatorname{binaryString}\left(s, t\right) = \operatorname{List.flatten}\left(\operatorname{List.ofFn}\left(\operatorname{fun} (i : \operatorname{Fin}\left(k\right)) \mapsto \operatorname{List.append}\left(\operatorname{List.replicate}\left(s\left(i\right), \operatorname{Bool.false}\right), \operatorname{List.replicate}\left(t\left(i\right), \operatorname{Bool.true}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.binaryString` (`✓ std3`).

*Citation.* Santanu Mandal, Ranjit Mehatari, and Kinkar Chandra Das (2022). *On the spectrum and energy of Seidel matrix for chain graphs*. DOI: [10.48550/arXiv.2205.00310](https://doi.org/10.48550/arXiv.2205.00310). URL: <https://arxiv.org/abs/2205.00310v1>.

*Commentary.*

Page 2, verbatim: We represent a chain graph $G$ on $n$ vertices using a binary string $b = \alpha_{1}\alpha_{2}\alpha_{3} ... \alpha_{n}$ of length $n$, where $\alpha_{i} = 0$ if the vertex $v_{i}$ is added as an isolated vertex, and $\alpha_{i} = 1$ if the vertex $v_{i}$ is dominating to all the previously added isolated vertices. As we start from a single vertex we always take $\alpha_{1} = 0$, and since we are considering connected graphs only so $\alpha_{n} = 1$. For any $n$ vertex chain graph, without loss of generality, we represent it by the binary string $b = 0^{s_{1}} 1^{t_{1}} 0^{s_{2}} ... 0^{s_{k}} 1^{t_{k}}$, where $s_{i}, t_{i}\geq 1$ and $\sum_{i = 1}^{k} (s_{i} + t_{i}) = n$. A chain graph is a bipartite graph, and it is complete bipartite if and only if $k = 1$.

The indices are Fin k; false is 0 and true is 1. List.ofFn orders the runs and List.flatten concatenates them.

**Definition 1.5 (The chain graph of a binary string).**

$$\forall (b : \operatorname{List}\left(\operatorname{Bool}\right)), \forall (i : \operatorname{Fin}\left(\operatorname{List.length}\left(b\right)\right)), \forall (j : \operatorname{Fin}\left(\operatorname{List.length}\left(b\right)\right)), (\operatorname{SimpleGraph.Adj}\left(\operatorname{chainGraph}\left(b\right), i, j\right)) \Leftrightarrow (((i < j) \land ((\operatorname{List.get}\left(b, i\right) = \operatorname{Bool.false}) \land (\operatorname{List.get}\left(b, j\right) = \operatorname{Bool.true}))) \lor ((j < i) \land ((\operatorname{List.get}\left(b, j\right) = \operatorname{Bool.false}) \land (\operatorname{List.get}\left(b, i\right) = \operatorname{Bool.true}))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.chainGraph` (`✓ std3`).

*Citation.* Santanu Mandal, Ranjit Mehatari, and Kinkar Chandra Das (2022). *On the spectrum and energy of Seidel matrix for chain graphs*. DOI: [10.48550/arXiv.2205.00310](https://doi.org/10.48550/arXiv.2205.00310). URL: <https://arxiv.org/abs/2205.00310v1>.

*Commentary.*

Page 2, verbatim: "adding an isolated vertex." "adding a vertex dominating to all previously added isolated vertices only." An earlier false position and a later true position are adjacent. The formula gives the entire adjacency relation, including its symmetric case and the absence of loops.

**Definition 1.6 (The Seidel matrix).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \operatorname{seidel}\left(G\right) = \operatorname{Matrix.of}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), 1 : \mathbb{R}\right)\right)\right) - 1 - \operatorname{HSMul.hSMul}\left(2 : \mathbb{R}, \operatorname{SimpleGraph.adjMatrix}\left(G, \mathbb{R}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.seidel` (`✓ std3`).

*Citation.* Santanu Mandal, Ranjit Mehatari, and Kinkar Chandra Das (2022). *On the spectrum and energy of Seidel matrix for chain graphs*. DOI: [10.48550/arXiv.2205.00310](https://doi.org/10.48550/arXiv.2205.00310). URL: <https://arxiv.org/abs/2205.00310v1>.

*Commentary.*

Page 2, verbatim: Let $G$ be a simple, connected, finite graph with vertex set $V = \{v_{1},v_{2},...,v_{n}\}$. Let $A$ be the (0,1)-adjacency matrix [12, 17] of $G$. Then the Seidel matrix [1, 2, 6, 9, 19, 20, 22, 23, 25] is a square matrix of order $n$ defined by $S = J - I - 2 \cdot A$, where $J$ is all $1$ matrix and $I$ is the identity matrix.

Here A is SimpleGraph.adjMatrix over the real numbers. The expression retains the all-ones matrix, identity matrix, and scalar multiple separately.

**Definition 1.7 (The comparison family).**

$$\forall (n : \mathbb{N}), \forall (k : \mathbb{N}), \forall (b : \operatorname{List}\left(\operatorname{Bool}\right)), \operatorname{Gamma}\left(n, k, b\right) = (\exists (s : \mathbb{N}), \exists (t : \mathbb{N}), (1 \le s) \land ((s \le n - 2 \cdot k + 1) \land ((1 \le t) \land ((t \le n - 2 \cdot k + 1) \land ((s + t = n - 2 \cdot k + 2) \land (b = \operatorname{List.append}\left(\operatorname{List.append}\left(\operatorname{List.replicate}\left(s, \operatorname{Bool.false}\right), \operatorname{List.flatten}\left(\operatorname{List.replicate}\left(k - 1, [\operatorname{Bool.true}, \operatorname{Bool.false}]\right)\right)\right), \operatorname{List.replicate}\left(t, \operatorname{Bool.true}\right)\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.Gamma` (`✓ std3`).

*Citation.* Santanu Mandal, Ranjit Mehatari, and Kinkar Chandra Das (2022). *On the spectrum and energy of Seidel matrix for chain graphs*. DOI: [10.48550/arXiv.2205.00310](https://doi.org/10.48550/arXiv.2205.00310). URL: <https://arxiv.org/abs/2205.00310v1>.

*Commentary.*

Page 21: Let $\Gamma_{n,k}$ be a class of chain graphs of order $n$ with the binary string $b= 0^{s_{1}} 1^{1} 0^{1} 1^{1} 0^{1}... 0^{1} 1^{t_{k}}$ such that $s_{1} + t_{k} = n - 2 \cdot k + 2$ with $1\leq s_{1}\leq n - 2 \cdot k + 1$ and $1\leq t_{k}\leq n - 2 \cdot k + 1$.

The middle word is k-1 copies of [true,false], representing the 2k-2 singleton runs under the source's underbrace. Natural subtraction is truncated; every parameter is a natural number.

**Definition 1.8 (Conjecture 4.14).**

$$\operatorname{claim} = (\forall (n : \mathbb{N}), \forall (k : \mathbb{N}), (1 \le k) \Rightarrow ((2 \cdot k \le n) \Rightarrow (\forall (s : \operatorname{Fin}\left(k\right) \to \mathbb{N}), \forall (t : \operatorname{Fin}\left(k\right) \to \mathbb{N}), (\forall (i : \operatorname{Fin}\left(k\right)), 1 \le s\left(i\right)) \Rightarrow ((\forall (i : \operatorname{Fin}\left(k\right)), 1 \le t\left(i\right)) \Rightarrow ((\operatorname{Finset.sum}\left(\operatorname{Finset.univ}, \operatorname{fun} (i : \operatorname{Fin}\left(k\right)) \mapsto s\left(i\right) + t\left(i\right)\right) = n) \Rightarrow (\forall (h : \operatorname{List}\left(\operatorname{Bool}\right)), (\operatorname{Gamma}\left(n, k, h\right)) \Rightarrow ((\operatorname{energy}\left(\operatorname{seidel}\left(\operatorname{chainGraph}\left(h\right)\right)\right) \le \operatorname{energy}\left(\operatorname{seidel}\left(\operatorname{chainGraph}\left(\operatorname{binaryString}\left(s, t\right)\right)\right)\right)) \land ((\operatorname{energy}\left(\operatorname{seidel}\left(\operatorname{chainGraph}\left(\operatorname{binaryString}\left(s, t\right)\right)\right)\right) = \operatorname{energy}\left(\operatorname{seidel}\left(\operatorname{chainGraph}\left(h\right)\right)\right)) \Leftrightarrow (\operatorname{Gamma}\left(n, k, \operatorname{binaryString}\left(s, t\right)\right))))))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.claim` (`✓ std3`).

*Citation.* Santanu Mandal, Ranjit Mehatari, and Kinkar Chandra Das (2022). *On the spectrum and energy of Seidel matrix for chain graphs*. DOI: [10.48550/arXiv.2205.00310](https://doi.org/10.48550/arXiv.2205.00310). URL: <https://arxiv.org/abs/2205.00310v1>.

*Commentary.*

Conjecture 4.14, page 25, verbatim: Let $G$ be a chain graph of order $n$ with the binary string $b = 0^{s_{1}} 1^{t_{1}} 0^{s_{2}} ... 0^{s_{k}} 1^{t_{k}}$ such that $\sum_{i = 1}^{k} (s_{i} + t_{i}) = n, s_{i}\geq 1 (1\leq i\leq k)$, and $t_{i}\geq 1 (1\leq i\leq k)$. Then $\operatorname{SE}\left(G\right)\geq \operatorname{SE}\left(H\right)$, where $H\in \Gamma_{n,k}$. Moreover, the equality holds if and only if $G\in \Gamma_{n,k}$.

The functions s,t have domain Fin k and positive natural values; n is their total. Every comparison binary string h in Gamma n k is quantified separately. The energy is the shared characteristic-root energy of the real Seidel matrix.

**Theorem 1.9 (Minimum energy and every equality case).**

$$\forall (n : \mathbb{N}), \forall (k : \mathbb{N}), (1 \le k) \Rightarrow ((2 \cdot k \le n) \Rightarrow (\forall (s : \operatorname{Fin}\left(k\right) \to \mathbb{N}), \forall (t : \operatorname{Fin}\left(k\right) \to \mathbb{N}), (\forall (i : \operatorname{Fin}\left(k\right)), 1 \le s\left(i\right)) \Rightarrow ((\forall (i : \operatorname{Fin}\left(k\right)), 1 \le t\left(i\right)) \Rightarrow ((\operatorname{Finset.sum}\left(\operatorname{Finset.univ}, \operatorname{fun} (i : \operatorname{Fin}\left(k\right)) \mapsto s\left(i\right) + t\left(i\right)\right) = n) \Rightarrow (\forall (h : \operatorname{List}\left(\operatorname{Bool}\right)), (\operatorname{Gamma}\left(n, k, h\right)) \Rightarrow ((\operatorname{energy}\left(\operatorname{seidel}\left(\operatorname{chainGraph}\left(h\right)\right)\right) \le \operatorname{energy}\left(\operatorname{seidel}\left(\operatorname{chainGraph}\left(\operatorname{binaryString}\left(s, t\right)\right)\right)\right)) \land ((\operatorname{energy}\left(\operatorname{seidel}\left(\operatorname{chainGraph}\left(\operatorname{binaryString}\left(s, t\right)\right)\right)\right) = \operatorname{energy}\left(\operatorname{seidel}\left(\operatorname{chainGraph}\left(h\right)\right)\right)) \Leftrightarrow (\operatorname{Gamma}\left(n, k, \operatorname{binaryString}\left(s, t\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/mmd2205-seidelchain` (proved) by `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mmd2205-seidelchain","declaration_gid":"D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Santanu Mandal, Ranjit Mehatari, and Kinkar Chandra Das (2022). *On the spectrum and energy of Seidel matrix for chain graphs*. DOI: [10.48550/arXiv.2205.00310](https://doi.org/10.48550/arXiv.2205.00310). URL: <https://arxiv.org/abs/2205.00310v1>.

*Commentary.*

Sign switching merges the first 0-run with the final 1-run. Compression gives a real symmetric odd core with weights at least one and first weight greater than one. Its trace-norm minimum and the constant inertia correction give the energy comparison. Equality forces every intermediate run to have length one, exactly the family Gamma. When k=1, switching a bipartition gives the all-ones matrix minus the identity for every graph in the comparison.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.Gamma`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.binaryString`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.chainGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.energy`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.energy_eigenvalues`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.seidel`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.sum_abs_eq_trace_sqrt`
- Dependency: [D5/S3/Observer/Hankel/BalancedHankelSchmidt](../../../Observer/Hankel/BalancedHankelSchmidt.md)
- Dependency: [D5/S3/Weil/ZetaLinear/FullRankInertiaPullback](../../../Weil/ZetaLinear/FullRankInertiaPullback.md)
