# The general three-seed family

## Abstract

Theorem 19 gives the full seeded greedy range and exact characteristic periodicity.

Theorem 19 establishes the eventual difference pattern for this family. The interval formula below expresses the same sequence as a set of integers. The least characteristic period and its earliest integer onset follow directly from that formula. A characteristic preperiod counts positive integer positions; the source's f+g+2 preperiod counts sequence entries and differences.

All number variables are natural. Write a=f+g, h=g+d, b=f+2g+d-1 and M=3f+5g+2d-3=3a+2h-3. Subtractions in the formulas are natural subtractions. Icc denotes a closed interval, mod denotes remainder, and a set used as a predicate denotes membership. The admitted domain is 1 <= f < g, d >= 2, f+g >= d+1, excluding only (1,2,2).

**Definition 1.1 (The initial and periodic blocks).**

$$\forall f, g, d: \mathbb{N}, \operatorname{A}\left(f, g, d\right) = \operatorname{union}\left(\operatorname{union}\left(\left\{f, g\right\}, \operatorname{Icc}\left(g + d, f + 2 \cdot g + d - 1\right)\right), \operatorname{union}_{t \ge 1} \operatorname{image}\left((r \mapsto t \cdot \left(3 \cdot f + 5 \cdot g + 2 \cdot d - 3\right) + r), \operatorname{Icc}\left(g + d - 2, f + 2 \cdot g + d - 1 - 2\right)\right)\right).$$

*Formalization.* `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.A` (`✓ std3`).

*Citation.* Daan van Berkel, Wieb Bosma (2026). *On t-sumfree sequences*. DOI: [10.48550/arXiv.2609.16843](https://doi.org/10.48550/arXiv.2609.16843). URL: <https://arxiv.org/html/2609.16843v1>.

*Commentary.*

The two isolated seeds precede I(0)=[h,b]. For every positive j, I(j)=jM+[h-2,b-2]. Each interval has f+g entries; the first omission block is two integers shorter than every subsequent omission block.

**Definition 1.2 (The literal greedy recurrence).**

$$\forall f, g, d: \mathbb{N}, \operatorname{greedyPrefix}\left(f, g, d, 0\right) = [g + d, g, f] \land (\forall n: \mathbb{N}, \operatorname{greedyPrefix}\left(f, g, d, n + 1\right) = \operatorname{cons}\left(\min \{z \in \mathbb{N} \mid \operatorname{headD}\left(\operatorname{greedyPrefix}\left(f, g, d, n\right), 0\right) < z \land \neg (\exists x, y, w: \mathbb{N}, (x < y \land y < w \land x \in \operatorname{greedyPrefix}\left(f, g, d, n\right) \land y \in \operatorname{greedyPrefix}\left(f, g, d, n\right) \land w \in \operatorname{greedyPrefix}\left(f, g, d, n\right) \land x + y + w = z))\}, \operatorname{greedyPrefix}\left(f, g, d, n\right)\right)).$$

*Formalization.* `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.greedyPrefix` (`✓ std3`).

*Citation.* Daan van Berkel, Wieb Bosma (2026). *On t-sumfree sequences*. DOI: [10.48550/arXiv.2609.16843](https://doi.org/10.48550/arXiv.2609.16843). URL: <https://arxiv.org/html/2609.16843v1>.

*Commentary.*

The list is stored in decreasing order. Starting from [h,g,f], each step prepends the least integer larger than the head that is not the sum of three distinct list entries. The distinctness condition is x<y<w, so repeated summands are forbidden. The minimum always exists: an integer larger than the head and three times the sum of the list cannot be such a sum.

**Definition 1.3 (The greedy sequence's range).**

$$\forall f, g, d, z: \mathbb{N}, \operatorname{S}\left(f, g, d, z\right) \Leftrightarrow \exists n: \mathbb{N}, z \in \operatorname{greedyPrefix}\left(f, g, d, n\right).$$

*Formalization.* `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.S` (`✓ std3`).

*Citation.* Daan van Berkel, Wieb Bosma (2026). *On t-sumfree sequences*. DOI: [10.48550/arXiv.2609.16843](https://doi.org/10.48550/arXiv.2609.16843). URL: <https://arxiv.org/html/2609.16843v1>.

*Commentary.*

Membership means occurrence in some literal greedy prefix. No periodic membership formula is used in the recurrence defining these prefixes.

**Theorem 1.4 (The exact restricted sum invariant).**

$$\forall f, g, d, z: \mathbb{N}, (1 \le f \land f < g \land 2 \le d \land d + 1 \le f + g \land (f \neq 1 \lor g \neq 2 \lor d \neq 2)) \implies (\operatorname{RestrictedThreeSum}\left(\operatorname{A}\left(f, g, d\right), z\right) \Leftrightarrow (g + d < z \land \neg (z \in \operatorname{A}\left(f, g, d\right)))).$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.restricted_three_sum_eq_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daan van Berkel, Wieb Bosma (2026). *On t-sumfree sequences*. DOI: [10.48550/arXiv.2609.16843](https://doi.org/10.48550/arXiv.2609.16843). URL: <https://arxiv.org/html/2609.16843v1>.

*Commentary.*

RestrictedThreeSum(P,n) means that x+y+w=n for x<y<w with all three entries in P, using the existing two-parameter definition. Four interval sum families cover the initial gap and every later gap uniformly in j. Conversely the sum of the three residues lies between b-1 and M+h-3. The top two residues b-1 and b occur only in the initial interval. Distinct periodic entries may share a residue; the bounds retain these cases. The exclusion (1,2,2) is needed at the last initial overlap, and both the boundary f+g=d+1 and every other d=2 case are included.

**Theorem 1.5 (The actual greedy range equals the block set).**

$$\forall f, g, d: \mathbb{N}, (1 \le f \land f < g \land 2 \le d \land d + 1 \le f + g \land (f \neq 1 \lor g \neq 2 \lor d \neq 2)) \implies (\operatorname{S}\left(f, g, d\right) = \operatorname{A}\left(f, g, d\right)).$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.s_eq_A` (`✓ std3`). ∎

*Citation.* Daan van Berkel, Wieb Bosma (2026). *On t-sumfree sequences*. DOI: [10.48550/arXiv.2609.16843](https://doi.org/10.48550/arXiv.2609.16843). URL: <https://arxiv.org/html/2609.16843v1>.

*Commentary.*

The prefix invariant states that every candidate up to the current head occurs in the prefix. The least-next-entry rule excludes any candidate between consecutive heads by the sum invariant. If the next head were not a candidate, that invariant would supply a forbidden triple of earlier entries. The heads grow at least by one at each step, proving the full range equality.

**Definition 1.6 (Characteristic periodicity from an integer position).**

$$\forall P: (\mathbb{N} \to \operatorname{Prop}), \forall q, N: \mathbb{N}, \operatorname{PeriodFrom}\left(P, q, N\right) \Leftrightarrow (\forall n: \mathbb{N}, N \le n \implies (P\left(n + q\right) \Leftrightarrow P\left(n\right))).$$

*Formalization.* `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.PeriodFrom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PeriodFrom(P,q,N) compares membership at n and n+q for every n >= N. It refers to integer positions, independently of the enumeration of P.

**Theorem 1.7 (All eventual periods and their earliest onset).**

$$\forall f, g, d, q, N: \mathbb{N}, (1 \le f \land f < g \land 2 \le d \land d + 1 \le f + g \land (f \neq 1 \lor g \neq 2 \lor d \neq 2)) \implies 0 < q \implies (\operatorname{PeriodFrom}\left(\operatorname{S}\left(f, g, d\right), q, N + 1\right) \Leftrightarrow (3 \cdot f + 5 \cdot g + 2 \cdot d - 3 \mid q \land f + 2 \cdot g + d - 1 \le N)).$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.characteristic_periods` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daan van Berkel, Wieb Bosma (2026). *On t-sumfree sequences*. DOI: [10.48550/arXiv.2609.16843](https://doi.org/10.48550/arXiv.2609.16843). URL: <https://arxiv.org/html/2609.16843v1>.

*Commentary.*

For n>b, membership is exactly h-2 <= n mod M <= b-2. This cyclic interval has a unique transition from zero to one. A shift preserving it fixes that transition, forcing divisibility by M. Moreover b belongs to the sequence, whereas b+q is absent for every positive multiple q of M. Thus the least positive eventual characteristic period is M, the least characteristic preperiod length is b, and the first periodic integer is b+1. This is a direct deduction from the range formula. For Example 20, (f,g,d)=(3,7,6), the blocks are [13,22], [64,73], [117,126], and so on; M=53 and characteristic periodicity starts at 23.

## References

- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.A`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.PeriodFrom`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.S`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.characteristic_periods`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.greedyPrefix`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.restricted_three_sum_eq_complement`
- Truth anchor: `D5/S1/Words/Sumfree/GreedyThreeSumfreeGeneralFamily.s_eq_A`
- Dependency: [D5/S1/Words/Sumfree/GreedyThreeSumfreeTwoParameter](GreedyThreeSumfreeTwoParameter.md)
