# Branch-Conditioned Trace Distance

## Abstract

A trace-nonincreasing finite Kraus branch contracts trace distance after weighting by its probability.

**Theorem 1.1 (Conditioning is stable above the branch-probability floor).**

$$\forall d: \operatorname{Nat}, iota: \operatorname{Type}, [\operatorname{Fintype}(iota)],\\{}rho: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), sigma: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), K: iota \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}),\\{}\operatorname{PosSemidef}(rho) \land \left(\operatorname{Tr}(rho) = 1 \land \left(\operatorname{PosSemidef}(sigma) \land \operatorname{Tr}(sigma) = 1\right)\right),\\{}\sum_{i \in iota} {K_{i}}^{*} \cdot K_{i} \le I_{d} \Rightarrow \operatorname{let} B: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}) = \sum_{i \in iota} {K_{i}}^{*} \cdot K_{i},\\{}Phi: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}) \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}) = X \mapsto \sum_{i \in iota} K_{i} \cdot X \cdot {K_{i}}^{*},\\{}p: \mathbb{R} = \operatorname{Re}(\operatorname{Tr}(rho \cdot B)), q: \mathbb{R} = \operatorname{Re}(\operatorname{Tr}(sigma \cdot B)),\\{}D: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}) \to \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}) \to \mathbb{R} = X, Y \mapsto \frac{\operatorname{traceNorm}(X - Y)}{2};\\{}\lvert p - q \rvert \le D(rho, sigma) \land \left(\left(\left(0 < p \land 0 < q\right) \Rightarrow \operatorname{max}(p, q) \cdot D(\frac{1}{p} \cdot Phi(rho), \frac{1}{q} \cdot Phi(sigma)) \le D(rho, sigma)\right) \land \left(\forall pStar \in \mathbb{R}, epsilon \in \mathbb{R},\; \left(0 < pStar \land \left(pStar \le p \land \left(D(rho, sigma) \le epsilon \land epsilon < pStar\right)\right)\right) \Rightarrow \left(0 < q \land D(\frac{1}{p} \cdot Phi(rho), \frac{1}{q} \cdot Phi(sigma)) \le \frac{epsilon}{pStar}\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/BranchConditionedTraceDistance.branch_conditioned_trace_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho and sigma be positive semidefinite matrices of trace one. A finite Kraus family defines a completely positive branch whose effect is bounded by the identity, and p and q are its probabilities on the two states.

The traceless Hermitian state difference splits into positive and negative parts of equal trace. Positivity of the branch and its complementary failure weight bounds both the probability change and the surviving trace-norm change by the original Jordan mass.

Normalizing the two branch outputs introduces an inverse probability. Weighting by the larger branch probability removes this denominator. A positive probability floor therefore turns an input error epsilon into conditioned error at most epsilon divided by that floor.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/BranchConditionedTraceDistance.branch_conditioned_trace_distance`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
