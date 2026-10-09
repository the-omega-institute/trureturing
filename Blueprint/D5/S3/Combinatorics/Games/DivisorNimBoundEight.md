# The Distinguished Heap Eight

## Abstract

Every positive position containing a heap of size eight has Sprague–Grundy value at most sixteen.

**Theorem 1.1 (Depth zero has value at most five).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, 0\right) \land \operatorname{mem}\left(8, P\right)\right)\right) \Rightarrow \operatorname{grundy}\left(P\right) \le 5$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundEight.eight_depth_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At depth zero, the unique odd heap is different from eight. Its legal removal amounts must divide eight, which has four positive divisors.

**Theorem 1.2 (Depth one has value at most ten).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, 1\right) \land \operatorname{mem}\left(8, P\right)\right)\right) \Rightarrow \operatorname{grundy}\left(P\right) \le 10$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundEight.eight_depth_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With a unique minimum, odd removals preserving eight have value at most five. Replacing eight leaves an odd heap at most seven; remainders at most five give value at most six, and the remainder seven also gives value at most six because two of its removal amounts give zero. There are at most three exceptional even removals. With several minimum heaps, the ordinary recurrence gives value at most nine.

**Theorem 1.3 (Depth two has value at most fourteen).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \left(\operatorname{Positive}\left(P\right) \land \left(\operatorname{HasDepth}\left(P, 2\right) \land \operatorname{mem}\left(8, P\right)\right)\right) \Rightarrow \operatorname{grundy}\left(P\right) \le 14$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundEight.eight_depth_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lower-depth followers have value at most eleven: the unchanged-eight bounds are five and ten, and the changed-eight bounds are eight and eleven. At most two exceptional removal values give the bound fourteen.

**Theorem 1.4 (Every position containing eight has value at most sixteen).**

$$\forall P \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \left(\operatorname{Positive}\left(P\right) \land \operatorname{mem}\left(8, P\right)\right) \Rightarrow \operatorname{grundy}\left(P\right) \le 16$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Games/DivisorNimBoundEight.eight_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The position depth is at most three. At depth three the preceding bounds give fourteen for every ordinary follower, and the unique possible exceptional removal gives sixteen.

## References

- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundEight.eight_bound`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundEight.eight_depth_one`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundEight.eight_depth_two`
- Truth anchor: `D5/S3/Combinatorics/Games/DivisorNimBoundEight.eight_depth_zero`
- Dependency: [D5/S3/Combinatorics/Games/DivisorNimBoundSmall](DivisorNimBoundSmall.md)
