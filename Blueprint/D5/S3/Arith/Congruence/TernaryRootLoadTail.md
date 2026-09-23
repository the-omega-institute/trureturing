# Ternary Root Load Tails

## Abstract

A finite sequence of ternary-root choices has a uniform discounted load-square bound.

**Theorem 1.1 (An explicit bound for every finite itinerary).**

$$\forall d0 \in \mathbb{R}, d1 \in \mathbb{R}, a \in \mathbb{N}, b \in \mathbb{N}, w \in List\left(Bool\right),\; \left(0 \le d0 \land 0 \le d1\right) \Rightarrow rootLoadTail\left(d0, d1, a, b, w\right) \le 3 \cdot max\left(d0 \cdot \left(a + 2\right), d1 \cdot \left(b + 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TernaryRootLoadTail.root_load_tail_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonnegative real numbers d0 and d1 bound the available densities in two ternary roots. Natural numbers a and b count earlier positive test depths assigned to each root. A finite Boolean list records all remaining choices, with false selecting the first root.

The function rootLoadTail is zero on an empty list. A false step adds (3 + 2a)d0, increases a by one, and divides the remaining cost by three; a true step adds (3 + 2b)d1 and similarly increases b. The coefficient three accounts for a diagonal term and two intersections with the constant test class. Previous tests in the same root contribute two each.

The bound holds for every finite length and every pair of initial counts. Induction on the itinerary preserves the explicit maximum of the two root potentials. In a ternary congruence calculation, initial counts a = 1 and b = 0 and the depth-two factor 1/9 give a remaining-cost bound max(d0, 2d1/3). Relating an actual residue layout to these choices and bounding its other prime coordinates require additional arguments.

## References

- Truth anchor: `D5/S3/Arith/Congruence/TernaryRootLoadTail.root_load_tail_le`
