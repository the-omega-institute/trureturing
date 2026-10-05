# Coordinates of Recursive Exponential Weights

## Abstract

Recursive exponential weights have explicit endpoint and interior coordinates for every real site sequence.

For any real sequence loss, edge(loss,i) is exp(-(loss(i+1)-loss(i))/2). The existing equilibriumWeight recursion starts with singleton weight one. At stage m+1 it retains each earlier coordinate except the former last, from which it subtracts edge(loss,m)/(1+edge(loss,m)); the new last coordinate is 1/(1+edge(loss,m)). No ordering assumption is needed to define this recursion.

**Theorem 1.1 (All coordinates at every size).**

$$\forall n \in \mathbb{N},\; \forall loss \in \mathbb{N} \to \mathbb{R},\; \operatorname{equilibriumWeight}\left(n + 1, loss, 0\right) = \frac{1}{1 + \operatorname{edge}\left(loss, 0\right)} \land \left(\operatorname{equilibriumWeight}\left(n + 1, loss, \operatorname{last}\left(n + 1\right)\right) = \frac{1}{1 + \operatorname{edge}\left(loss, n\right)} \land \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{equilibriumWeight}\left(n + 1, loss, \operatorname{succ}\left(\operatorname{castSucc}\left(i\right)\right)\right) = \frac{1}{1 + \operatorname{edge}\left(loss, i\right)} + \frac{1}{1 + \operatorname{edge}\left(loss, i + 1\right)} - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ExponentialSectorKernelEquilibriumWeights.equilibrium_weight_endpoint_interior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stage n+1 has n+2 coordinates, indexed by Fin(n+2). Its first index is zero and its last is Fin.last(n+1). For i in Fin(n), succ(castSucc(i)) is the interior index i+1; the adjacent coefficients are edge(loss,i) and edge(loss,i+1). In edge(loss,i), the Fin index is coerced to its natural value.

Induction preserves the initial coordinate whenever a later site is appended. An old interior coordinate is also preserved. The former endpoint becomes a new interior coordinate, and subtracting the new correction gives the displayed sum of the two adjacent reciprocals minus one. Exponentials are positive, so every denominator 1+edge(loss,i) is nonzero.

For n=0 this is the two-site stage: both endpoint weights are 1/(1+edge(loss,0)), and the interior quantifier over Fin(0) is empty. The singleton stage has weight one and lies outside this reindexing.

For strictly increasing ordered sites, the ordered-kernel row equations and positivity identify these recursive weights with the positive equilibrium vector. With the inverse kernel on those distinct sites, Kv=1 gives v=K inverse times the ones vector. Normalization by its positive total mass gives the ordered simplex point. For arbitrary loss the coordinate statement gives no weight positivity or probability interpretation; physical channel optimality requires its separate channel identification.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ExponentialSectorKernelEquilibriumWeights.equilibrium_weight_endpoint_interior`
- Dependency: [D5/S3/Quantum/Entanglement/ExponentialSectorKernel](ExponentialSectorKernel.md)
