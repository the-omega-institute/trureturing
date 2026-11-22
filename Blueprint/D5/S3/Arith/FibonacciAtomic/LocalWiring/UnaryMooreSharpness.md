# Sharp uniform prefix separation for unary Moore sources

## Abstract

At every shorter length two unary Moore sources with at most K states can agree throughout the prefix and disagree on its next output. Thus 2K−1 is the least uniform sufficient prefix length.

**Theorem 1.1 (Actual unary witness machines for every shorter prefix).**

$$(1\le K \land 0\le v<2K-1) \implies \exists s,t \in \mathcal{M}_{K}, (\forall i<v, s_{i}=t_{i}) \land s_{v}\neq t_{v}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LocalWiring/UnaryMooreSharpness.unary_moore_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both tables are autonomous and unary, with one actual start state and one Boolean output per state. The initial state's output is index zero. The public bound K is positive and each table uses at most K states.

At K=1 the one-state machines have opposite constant labels. Otherwise use a K-cycle and a source with a transient state zero feeding the cycle on states one through K−1. Both first emit one at K−1, and the second source, but not the first, emits one at 2K−2.

For the requested cut v, advance each start along its own actual transition by 2K−2−v. The shifted trajectories agree at every index below v and emit opposite bits at v. Together with the frozen upper bound this proves the uniform threshold, not a fixed hard pair across all cuts or a statement about comparative observation costs.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LocalWiring/UnaryMooreSharpness.unary_moore_sharpness`
- Dependency: [D5/S3/Arith/FibonacciAtomic/LocalWiring/UnaryMooreSeparation](UnaryMooreSeparation.md)
