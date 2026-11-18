# Square-summable natural-floor step functions

## Abstract

A square-summable real sequence on the positive natural indices defines an L2 natural-floor step function on the Lebesgue half-line (1,infinity).

**Theorem 1.1 (From sequence squares to half-line L2 membership).**

$$\forall a:\mathbb{N}\to\mathbb{R}, \operatorname{Summable}\left((n\mapsto \operatorname{a}\left(n+1\right)^{2})\right)\Rightarrow \operatorname{MemLp}\left((x\mapsto \operatorname{a}\left(\operatorname{NatFloor}\left(x\right)\right)), 2, \operatorname{volume}\left(\right)\mid(1,\infty)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Measure/NatFloorL2.memLp_nat_floor_of_summable_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a : N -> R, assume that the real series of a(n+1)^2 is summable. Then x |-> a(Nat.floor x) belongs to MemLp with exponent 2 for Lebesgue volume restricted to (1,infinity). NatFloor in the formula denotes the natural-valued floor. There is no condition on a(0), no sign condition, and no finite support assumption.

The countably many cells [n+1,n+2), n in N, cover [1,infinity). On the nth cell the floor is n+1, so the squared step function is constant and its integral is a(n+1)^2. The summable cell integrals give genuine integrability on the union by integrableOn_iUnion_of_summable_integral_norm. Restriction to (1,infinity), measurability of the natural floor, and memLp_two_iff_integrable_sq give the conclusion. This is a reusable analytic transfer, with no claim of literature priority.

## References

- Truth anchor: `D5/S3/Analytic/Measure/NatFloorL2.memLp_nat_floor_of_summable_sq`
