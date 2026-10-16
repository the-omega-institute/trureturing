# Complete span and endpoint balance

## Abstract

Anchored square partitions have exact difference-span, missing-membership and endpoint balances.

A square of side q consists of all ordered pairs (a,b) with both coordinates in Fin q. An attained label t names the class containing (t,t). Every cell belongs to exactly one label, and no class contains two cells with the same signed difference a-b. These conditions admit arbitrary class sizes and coordinate orders.

**Definition 1.1 (The complete square).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.Cell`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.Cell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cell(q) is Fin q times Fin q. The first coordinate is a and the second is b.

**Definition 1.2 (Signed original difference).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.difference`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.difference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every square cell x=(a,b), difference(x) is the integer a-b, with both coordinates cast to the integers before subtraction.

**Definition 1.3 (One simultaneous cover).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.Cover`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.Cover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cover(q) consists of a total label map from the complete square to Fin q, the equations label(t,t)=t for every t, and injectivity of the pair (label(x),difference(x)). Its fibers are pairwise disjoint and cover the square; the diagonal equations make every label attained. Conversely a disjoint complete cover with one diagonal anchor per class and injective differences supplies this label map.

**Definition 1.4 (Whole classes).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.cells`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.cells` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C:Cover(q) and t:Fin q, cells(C,t) is the finite set of all square cells labeled t.

**Definition 1.5 (Occupied differences).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.occupied`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.occupied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C and t, occupied(C,t), denoted D(t), is the image of cells(C,t) under difference. It contains zero, and its cardinality equals the cardinality of that entire class.

**Definition 1.6 (Lower occupied endpoint).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.lower`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.lower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C and t, lower(C,t), denoted L(t), is the minimum of D(t). Its range is 1-q through zero.

**Definition 1.7 (Upper occupied endpoint).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.upper`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.upper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C and t, upper(C,t), denoted U(t), is the maximum of D(t). Its range is zero through q-1.

**Definition 1.8 (Class cardinality).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.size`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.size` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C and t, size(C,t), denoted m(t), is the integer cast of the cardinality of cells(C,t).

**Definition 1.9 (The inherited size defect).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.defect`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.defect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C and t, defect(C,t), denoted delta(t), is 19-m(t). The balance theorem does not assume this value is nonnegative.

**Definition 1.10 (Missing integers in one span).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.gap`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C and t, gap(C,t), denoted g(t), is U(t)-L(t)+1-m(t). It is exactly the number of integers in the closed interval from L(t) to U(t) that are not in D(t).

**Definition 1.11 (Total class gaps).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.totalGap`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.totalGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C, totalGap(C), denoted G, is the sum of g(t) over all t:Fin q. Missing integers are counted separately for each class.

**Definition 1.12 (Classes supplying one difference).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.supplied`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.supplied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C and integer j, supplied(C,j) is the set of labels t for which j belongs to D(t).

**Definition 1.13 (Classes spanning one integer).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.spanning`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.spanning` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C and integer j, spanning(C,j) is the set of labels t for which L(t) is at most j and j is at most U(t).

**Definition 1.14 (Missing class memberships).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.missing`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.missing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C and integer j, missing(C,j) is the subset of spanning(C,j) whose classes do not contain the occupied difference j. Such a membership is not an uncovered cell.

**Definition 1.15 (Span incidence).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.spanCount`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.spanCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C and integer j, spanCount(C,j), denoted nu(C,j), is the integer cardinality of spanning(C,j).

**Definition 1.16 (Gap incidence).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.holeCount`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.holeCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C and integer j, holeCount(C,j), denoted h(C,j), is the integer cardinality of missing(C,j).

**Definition 1.17 (Lower endpoint incidence).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.starts`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.starts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C and integer j, starts(C,j), denoted A(C,j), counts labels t with L(t)=j.

**Definition 1.18 (Upper endpoint incidence).**

Lean statement: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.ends`

*Formalization.* `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.ends` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every C and integer j, ends(C,j), denoted B(C,j), counts labels t with U(t)=j.

**Theorem 1.19 (All span and endpoint identities).**

$$\forall q \in \mathbb{N},\; \forall C \in \operatorname{Cover}\left(q\right),\; (\forall j \in \mathbb{Z},\; (\lvert j \rvert < q) \Rightarrow (\operatorname{nu}\left(C, j\right) = q - \lvert j \rvert + \operatorname{h}\left(C, j\right))) \land ((\operatorname{h}\left(C, 0\right) = 0) \land ((\operatorname{h}\left(C, 1 - q\right) = 0) \land ((\operatorname{h}\left(C, q - 1\right) = 0) \land ((\forall j \in \mathbb{Z},\; (\lvert j \rvert < q) \Rightarrow ((0 \le \operatorname{h}\left(C, j\right)) \land (\operatorname{h}\left(C, j\right) \le \lvert j \rvert))) \land ((\forall j \in \mathbb{Z},\; ((j < 1 - q) \lor (q - 1 < j)) \Rightarrow (\operatorname{h}\left(C, j\right) = 0)) \land ((\operatorname{G}\left(C\right) = \sum_{j \in \operatorname{Icc}\left(1 - q, q - 1\right)} \operatorname{h}\left(C, j\right)) \land ((\forall j \in \mathbb{Z},\; ((1 - q \le j) \land (j \le 0)) \Rightarrow (\operatorname{A}\left(C, j\right) = 1 + \operatorname{h}\left(C, j\right) - \operatorname{h}\left(C, j - 1\right))) \land ((\forall j \in \mathbb{Z},\; ((0 \le j) \land (j \le q - 1)) \Rightarrow (\operatorname{B}\left(C, j\right) = 1 + \operatorname{h}\left(C, j\right) - \operatorname{h}\left(C, j + 1\right))) \land ((\forall t \in \operatorname{Fin}\left(q\right),\; \operatorname{U}\left(C, t\right) - \operatorname{L}\left(C, t\right) = 18 - \operatorname{delta}\left(C, t\right) + \operatorname{g}\left(C, t\right)) \land ((\sum_{t \in \operatorname{Fin}\left(q\right)} (\operatorname{U}\left(C, t\right) - \operatorname{L}\left(C, t\right)) = q \cdot \left(q - 1\right) + \operatorname{G}\left(C\right)) \land (\forall k \in \mathbb{Z},\; ((0 < k) \land (k < q)) \Rightarrow ((\operatorname{high}\left(C, k\right) = k - \operatorname{h}\left(C, k\right)) \land (\operatorname{low}\left(C, k\right) = k - \operatorname{h}\left(C, 0 - k\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.complete_span_endpoint_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The assertion ranges over every natural q and every C:Cover(q); in particular it includes all positive side lengths. In the formula L(C,t), U(C,t), delta(C,t), g(C,t), and G(C) denote the definitions above. The functions low(C,k) and high(C,k) count, respectively, labels with -L(t)<k and U(t)<k. The finite sum of h over Icc(1-q,q-1) is its sum over all integers, because the displayed support assertion proves that every other summand is zero.

For a nonnegative difference k<q, its band is in bijection with Fin(q-k): send i to (i+k,i). Swapping the coordinates gives the corresponding negative band. Sending a band cell to its actual label is another bijection, since complete coverage supplies the label and difference injectivity separates the cells. Thus exactly q-|j| labels supply difference j. Every span incidence is either one of these supplied memberships or a missing membership, which gives the first equation and the bound on h.

Zero belongs to every occupied set. An extreme difference lying in a span must equal its occupied endpoint, so the three boundary hole counts vanish. Counting the missing pairs (t,j) in the two orders gives G. Below zero no span ends, and above zero no span begins; successive span incidences therefore differ by the appropriate endpoint incidence. These statements include endpoints at zero, where a singleton span contributes to both A and B. At 1-q and q-1 the adjacent outside incidence is zero.

The per-class identity follows from the actual span length and class cardinality. The complete partition contains q squared cells, so summing subtracts exactly q class baselines and yields q(q-1)+G. Subtracting the positive or negative span incidence from q gives both cumulative endpoint balances.

For the native-alpha recut covers, take the actual original pair (a,b), the diagonal anchor label t, and the entire class C(t). Every cover of either lag family has the three geometric properties in Cover(q), so this theorem gives the complete span and endpoint conclusion on that whole domain, including fused nonmonotone classes and every defect allocation at eighteen labels. At q=18 the total is 306+G; at q=19 it is 342+G. No native service existence, cover existence, controller bound, or physical cost follows from these necessary counting identities.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.Cell`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.Cover`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.cells`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.complete_span_endpoint_balance`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.defect`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.difference`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.ends`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.gap`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.holeCount`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.lower`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.missing`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.occupied`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.size`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.spanCount`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.spanning`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.starts`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.supplied`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.totalGap`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AnchoredSquareSpanBalance.upper`
