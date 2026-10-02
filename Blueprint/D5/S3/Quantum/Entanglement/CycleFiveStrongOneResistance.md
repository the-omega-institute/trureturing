# The five-cycle graph state is strongly 1-resistant

## Abstract

The five-cycle graph state is genuinely multipartite entangled, remains genuinely multipartite entangled after any one-qubit loss, and becomes fully separable after any two-qubit loss.

**Definition 1.1 (The C5 clause of the published question).**

$$claim = \operatorname{IsStrongResistant}\left(1, \operatorname{cycleGraphState}\left(5\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/CycleFiveStrongOneResistance.claim` (`✓ std3`).

*Citation.* Zicheng Han; Wanchen Zhang; Xiande Zhang (2026). *A five-qubit 1-resistant graph state and stabilizer marginal certificates*. URL: <https://arxiv.org/abs/2606.08561v1>.

*Commentary.*

Han, Zhang and Zhang, arXiv:2606.08561v1, page 8, Discussion: "Several open problems remain. First, do C₅ and C₆ give strongly m-resistant graph states for m = 1 and m = 2, respectively? Here, “strong” means genuine multipartite entanglement rather than mere entanglement." This claim is the C5, m = 1 clause. The imported cycleGraphState labels qubits by Fin 5, numbered 0,...,4, with amplitudes (-1) raised to the cyclic sum of adjacent bit products, divided by sqrt(32). The imported strong-resistance predicate requires initial genuine multipartite entanglement, genuine multipartite entanglement of every one-qubit-loss marginal, and full separability of every two-qubit-loss marginal. GME excludes finite convex mixtures of products across arbitrary nontrivial bipartitions, including mixtures whose cuts differ between terms. Full separability is a finite convex mixture of products of single-qubit positive semidefinite trace-one density matrices.

**Theorem 1.2 (Strong 1-resistance of the five-cycle state).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CycleFiveStrongOneResistance.result` (`✓ std3`). ∎

*Resolves.* `Problems/han-zhang-zhang-2026-cycle-five-strong-one-resistance` (proved) by `D5/S3/Quantum/Entanglement/CycleFiveStrongOneResistance.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"han-zhang-zhang-2026-cycle-five-strong-one-resistance","declaration_gid":"D5/S3/Quantum/Entanglement/CycleFiveStrongOneResistance.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zicheng Han; Wanchen Zhang; Xiande Zhang (2026). *A five-qubit 1-resistant graph state and stabilizer marginal certificates*. URL: <https://arxiv.org/abs/2606.08561v1>.

*Acknowledgement.* Wanchen Zhang; Zicheng Han; Fei Shi; Xiande Zhang (2025). *New constructions of multipartite entanglement resistant to particle loss*. URL: <https://arxiv.org/abs/2505.06567v1>.

*Commentary.*

For the initial density matrix rho5 use W = I/2 - rho5; for each four-qubit marginal rho4 use W = I/2 - 2 rho4. In every case the expectation is -1/2, and the partial transpose of W is positive semidefinite across every nontrivial cut. Exact nonnegative graph-basis Gram decompositions establish this positivity. Reindexing the trace pairing shows that these witnesses have nonnegative expectation on each cut-product density matrix and hence on every biseparable mixture, so their negative expectation proves genuine multipartite entanglement. The finite checks include all 30 oriented cuts on five qubits and all 14 oriented cuts for each of the five four-qubit marginals. For each of the ten two-qubit loss sets, the three-qubit marginal is an equal mixture of four product states chosen from local Pauli eigenstates; the four weights are 1/4. All three clauses of strong resistance follow.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/CycleFiveStrongOneResistance.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/CycleFiveStrongOneResistance.result`
- Dependency: [D5/S3/Quantum/Entanglement/CycleSixStrongTwoResistanceRefutation](CycleSixStrongTwoResistanceRefutation.md)
