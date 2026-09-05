# The Erdos-Moser Local Prime Obstruction

## Abstract

Moser's local prime obstruction makes the predecessor of every Erdos-Moser solution squarefree.

**Theorem 1.1 (Every prime divisor of the predecessor satisfies Moser's obstruction).**

$$\begin{aligned}\forall m, k \in \mathbb{N},\\1 < m \land 0 < k \land \sum_{i \in \operatorname{range}\left(m\right)} i^{k} = m^{k} \Rightarrow\\(\forall p \in \mathbb{N},\ \operatorname{Prime}\left(p\right) \Rightarrow p \mid (m - 1) \Rightarrow ((p - 1) \mid k \land p \mid (\lfloor(m - 1) / p\rfloor + 1) \land \neg p^{2} \mid (m - 1))) \land \operatorname{Squarefree}\left(m - 1\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Obstructions/ErdosMoserLocalObstruction.erdos_moser_local_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each prime p dividing m - 1, write q for the natural-number quotient (m - 1) / p. The displayed floor notation denotes this integer quotient, never rational division.

The proof partitions the power sum into q complete residue blocks in ZMod p, explicitly transports the residue range to ZMod p and then to its unit group, and applies the finite-field power-sum dichotomy. The zero branch is impossible, while the minus-one branch gives p dividing q + 1.

If p squared also divided m - 1, exact natural division would make p divide q, contradicting p dividing q + 1. The resulting exclusion for every prime is precisely squarefreeness. No parity assumption on k is used, and no claim is made that the open Erdos-Moser equation has no further solutions.

## References

- Truth anchor: `D5/S3/PrimeForms/Obstructions/ErdosMoserLocalObstruction.erdos_moser_local_obstruction`
