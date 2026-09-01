# Congruence Closure Duality

## Abstract

Forward congruences have dual repairs, common fixed points, and an adjoint triple.

**Theorem 1.1 (Dual canonical repairs of an equivalence relation).**

$$\begin{gathered}\forall Y: \operatorname{Type}, F: Y \to Y,\\\forall R: \operatorname{Setoid}(Y),\\\operatorname{I}(F, R) = R \iff \operatorname{IsForwardCongruence}(F, R) \iff \operatorname{C}(F, R) = R,\\\operatorname{I}(F, R) \subseteq R \land R \subseteq \operatorname{C}(F, R),\\\operatorname{GaloisConnection}(closureRepair, inclusion) \land \operatorname{GaloisConnection}(inclusion, interiorRepair).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/CongruenceClosureDuality.dual_congruence_repair_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equivalence relations on Y are ordered by relation inclusion. The predictive interior reuses the all-iterate congruence kernel, while the forgetting closure is the least stable setoid above its input.

The theorem proves contraction, monotonicity, and idempotence for the interior; extensivity, monotonicity, and idempotence for the closure; the common fixed-point characterization; both Galois connections; and the repair sandwich.

## References

- Truth anchor: `D5/S3/Observer/Separation/CongruenceClosureDuality.dual_congruence_repair_laws`
- Dependency: [D5/S3/Observer/Separation/CongruenceKernel](CongruenceKernel.md)
