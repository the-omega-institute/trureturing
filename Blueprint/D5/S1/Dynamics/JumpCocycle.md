# Hidden-Fiber Jump Cocycle

## Abstract

Hidden-fiber jump legality is exactly cocycle consistency.

<a id="describe-hidden-fiber-jump-cocycle"></a>

**Theorem 1.1 (Hidden-fiber jump legality is cocycle consistency).**

$$s_{\beta}=s_{\alpha}+\iota(k_{\alpha\beta}),\quad s_{\gamma}=s_{\beta}+\iota(k_{\beta\gamma})\Rightarrow \left(s_{\gamma}=s_{\alpha}+\iota(k_{\alpha\gamma})\Leftrightarrow k_{\alpha\gamma}=k_{\alpha\beta}+k_{\beta\gamma}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/JumpCocycle.jump_cocycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over a nonempty indexing domain, the visible circle projection is a surjective additive homomorphism. An additive equivalence identifies the product of all p-adic integer fibers with its kernel. Two realized hidden jumps connect three local lifts. Kernel membership first forces all three lifts to have the same visible projection.

A proposed direct jump is legal when translating the first lift by that jump reaches the third lift. This endpoint condition is independent of the cocycle equation. Cancelling the first lift, applying additivity, and using injectivity of the kernel equivalence prove that endpoint legality is equivalent to the pointwise sum of the two intervening jumps. Any disagreement therefore supplies an explicit endpoint residual and cannot be a legal motion.

## References

- Truth anchor: `D5/S1/Dynamics/JumpCocycle.jump_cocycle`
