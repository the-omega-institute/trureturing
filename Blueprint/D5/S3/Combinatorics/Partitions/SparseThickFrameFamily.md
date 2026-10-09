# Separated thick-frame word family

## Abstract

Exact-area thick frames, separated width and height grids, and an actual common word family.

**Definition 1.1 (The ceiling square side).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.side`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.side` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

side(k)=Nat.sqrt(k−1)+1. For positive k this is the ceiling of the square root, including perfect squares.

**Definition 1.2 (Variable frame thickness).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.thickness`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.thickness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

thickness(k,U)=(k+U−1)/U in natural division. For positive U this is the ceiling of k/U.

**Definition 1.3 (Exact grid size).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.gridCount`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.gridCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

gridCount(U,h)=(floor(U/6)−floor((U+7)/8))/(128h)+1. For U≥4096 and h>0 the natural subtraction does not truncate.

**Definition 1.4 (Width and height grid points).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.grid`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.grid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

grid(U,h,i)=floor((U+7)/8)+128h i for every i in Fin(gridCount(U,h)). For U≥4096 and h>0 all points lie between ceil(U/8) and floor(U/6), and successive points differ by 128h.

**Definition 1.5 (The maximal dyadic core level).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.level`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.level` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

level(k)=Nat.log2(1+side(k)/560). Its radix q=2^level(k) satisfies 8 coreSide(level(k))≤side(k) and side(k)<1120q.

**Definition 1.6 (The exact residual area).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.residualArea`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.residualArea` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For r=thickness(k,U) and s=thickness(k,V), residualArea(k,U,V,L,H)=k−(rL+sH)+rs. Under the large-area sparse hypotheses, both grids satisfy rL+sH≤k before the natural subtraction is used, and h²≤8t≤7h².

**Definition 1.7 (Rows of one thick frame).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.frameRows`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.frameRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

frameRows(r,s,L,H,h,mu) consists of r copies of L, the h actual rows of mu translated by s, and H−r−h copies of s. If mu is sorted, has length h and has every row at most h, then L≥s+h and H≥r+h make this a sorted Ferrers partition of height H. Both statistics refer to this same partition.

**Definition 1.8 (The full independent index domain).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.FrameIndex`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.FrameIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FrameIndex(k,U,V)=Fin(gridCount(U,side(k))) × Fin(gridCount(V,side(k))) × CoreIndex(level(k)). All width, height and both radix-eight coordinates are retained.

**Definition 1.9 (The actual framed square rows).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.sourceRows`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.sourceRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the large-area sparse hypotheses, choose L,H from the two indices, set t=residualArea(k,U,V,L,H), and apply the existing W(level(k),side(k),t,x) square-word construction. Its direct rows, without changing t or reversing the square core, are inserted in frameRows.

**Definition 1.10 (The word in the original dimensions).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.sourceWord`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.sourceWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the large-area sparse hypotheses with U=min(u,k) and V=min(v,k), append zero rows until there are v rows and apply wordOfRows with width u. The result has exactly u true letters, v false letters and scattered true-false area k.

**Definition 1.11 (The absolute constant).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.c0`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.c0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

c0=1/(6144² 1120⁶), independent of every dimension, area and aspect ratio.

**Theorem 1.12 (An actual globally separated joint family).**

$$\forall u \in \mathbb{N}, \forall v \in \mathbb{N}, \forall k \in \mathbb{N}, (4096 \leq k) \land (4096 \times k \leq (u)^{2}) \land (4096 \times k \leq (v)^{2}) \implies (\forall x \in \operatorname{FrameIndex}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right)\right), (\operatorname{sourceWord}\left(u, v, k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right) \in \operatorname{wordFiber}\left(u, v, k\right)) \land (\operatorname{count}\left(\operatorname{sourceWord}\left(u, v, k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right), true\right) = u) \land (\operatorname{count}\left(\operatorname{sourceWord}\left(u, v, k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right), false\right) = v) \land (\operatorname{scatteredTrueFalseCount}\left(\operatorname{sourceWord}\left(u, v, k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right) = k) \land (\operatorname{rows}\left(\operatorname{sourceWord}\left(u, v, k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right) = \operatorname{append}\left(\operatorname{sourceRows}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right), \operatorname{replicate}\left(v - \operatorname{length}\left(\operatorname{sourceRows}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right), 0\right)\right)) \land (\operatorname{length}\left(\operatorname{sourceRows}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right) = \operatorname{grid}\left(\operatorname{min}\left(v, k\right), \operatorname{side}\left(k\right), \operatorname{fst}\left(\operatorname{snd}\left(x\right)\right)\right)) \land (\operatorname{SortedGE}\left(\operatorname{sourceRows}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right)) \land (\forall a \in \operatorname{sourceRows}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right), a \leq \operatorname{grid}\left(\operatorname{min}\left(u, k\right), \operatorname{side}\left(k\right), \operatorname{fst}\left(x\right)\right)) \land (\operatorname{sum}\left(\operatorname{sourceRows}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right) = k) \land (\operatorname{thickness}\left(k, \operatorname{min}\left(u, k\right)\right) \times (\operatorname{grid}\left(\operatorname{min}\left(u, k\right), \operatorname{side}\left(k\right), \operatorname{fst}\left(x\right)\right))^{2} \leq \operatorname{squareRows}\left(\operatorname{sourceRows}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right)) \land (\operatorname{squareRows}\left(\operatorname{sourceRows}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right) \leq \operatorname{thickness}\left(k, \operatorname{min}\left(u, k\right)\right) \times (\operatorname{grid}\left(\operatorname{min}\left(u, k\right), \operatorname{side}\left(k\right), \operatorname{fst}\left(x\right)\right))^{2} + 7 \times k \times \operatorname{side}\left(k\right)) \land (\operatorname{thickness}\left(k, \operatorname{min}\left(v, k\right)\right) \times (\operatorname{grid}\left(\operatorname{min}\left(v, k\right), \operatorname{side}\left(k\right), \operatorname{fst}\left(\operatorname{snd}\left(x\right)\right)\right))^{2} \leq \operatorname{oddRows}\left(\operatorname{sourceRows}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right)) \land (\operatorname{oddRows}\left(\operatorname{sourceRows}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right) \leq \operatorname{thickness}\left(k, \operatorname{min}\left(v, k\right)\right) \times (\operatorname{grid}\left(\operatorname{min}\left(v, k\right), \operatorname{side}\left(k\right), \operatorname{fst}\left(\operatorname{snd}\left(x\right)\right)\right))^{2} + 7 \times k \times \operatorname{side}\left(k\right))) \land (\operatorname{Injective}\left(\operatorname{fun}\left(x:\operatorname{FrameIndex}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right)\right), \operatorname{Pair}\left(\operatorname{squareRows}\left(\operatorname{sourceRows}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right), \operatorname{oddRows}\left(\operatorname{sourceRows}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right)\right)\right)\right)) \land (\operatorname{Injective}\left(\operatorname{fun}\left(x:\operatorname{FrameIndex}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right)\right), \operatorname{Pair}\left(\operatorname{e}\left(\operatorname{G}\left(\operatorname{sourceWord}\left(u, v, k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right)\right), \operatorname{f}\left(\operatorname{G}\left(\operatorname{sourceWord}\left(u, v, k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right)\right)\right)\right)\right)) \land (\operatorname{Injective}\left(\operatorname{fun}\left(x:\operatorname{FrameIndex}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right)\right), \operatorname{sourceWord}\left(u, v, k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right)\right)) \land (\operatorname{ncard}\left(\operatorname{range}\left(\operatorname{fun}\left(x:\operatorname{FrameIndex}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right)\right), \operatorname{sourceWord}\left(u, v, k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right)\right)\right) = \operatorname{gridCount}\left(\operatorname{min}\left(u, k\right), \operatorname{side}\left(k\right)\right) \times \operatorname{gridCount}\left(\operatorname{min}\left(v, k\right), \operatorname{side}\left(k\right)\right) \times (\operatorname{q}\left(\operatorname{level}\left(k\right)\right))^{6}) \land (\operatorname{ncard}\left(\operatorname{range}\left(\operatorname{fun}\left(x:\operatorname{FrameIndex}\left(k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right)\right), \operatorname{Pair}\left(\operatorname{e}\left(\operatorname{G}\left(\operatorname{sourceWord}\left(u, v, k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right)\right), \operatorname{f}\left(\operatorname{G}\left(\operatorname{sourceWord}\left(u, v, k, \operatorname{min}\left(u, k\right), \operatorname{min}\left(v, k\right), x\right)\right)\right)\right)\right)\right)\right) = \operatorname{gridCount}\left(\operatorname{min}\left(u, k\right), \operatorname{side}\left(k\right)\right) \times \operatorname{gridCount}\left(\operatorname{min}\left(v, k\right), \operatorname{side}\left(k\right)\right) \times (\operatorname{q}\left(\operatorname{level}\left(k\right)\right))^{6}) \land (\operatorname{gridCount}\left(\operatorname{min}\left(u, k\right), \operatorname{side}\left(k\right)\right) \times \operatorname{gridCount}\left(\operatorname{min}\left(v, k\right), \operatorname{side}\left(k\right)\right) \times (\operatorname{q}\left(\operatorname{level}\left(k\right)\right))^{6} \leq \operatorname{capacity}\left(u, v, k\right)) \land (\operatorname{min}\left(u, k\right) \leq 6144 \times \operatorname{side}\left(k\right) \times \operatorname{gridCount}\left(\operatorname{min}\left(u, k\right), \operatorname{side}\left(k\right)\right)) \land (\operatorname{min}\left(v, k\right) \leq 6144 \times \operatorname{side}\left(k\right) \times \operatorname{gridCount}\left(\operatorname{min}\left(v, k\right), \operatorname{side}\left(k\right)\right)) \land (\operatorname{side}\left(k\right) < 1120 \times \operatorname{q}\left(\operatorname{level}\left(k\right)\right)) \land (k \leq (\operatorname{side}\left(k\right))^{2}) \land (\operatorname{c0}\left(\right) \times \operatorname{min}\left(u, k\right) \times \operatorname{min}\left(v, k\right) \times (k)^{2} \leq \operatorname{capacity}\left(u, v, k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.separated_frame_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put U=min(u,k), V=min(v,k) and h=side(k). The sparse hypotheses derive U,V≥4096, U,V≥32h, 1≤r,s≤h, k≤rU,sV≤2k, and 1024rs≤k. Every grid frame fits, and its exact residual area satisfies the existing square_family hypotheses. No core existence or grid cardinality is assumed.

For mu=rows(W), the two frame formulas are P=rL²+(H−r)s²+2st+squareRows(mu) and R=sH²+(L−s)r²+2rt+oddRows(mu). The direct row recursion gives 0≤squareRows(mu)≤ht and 0≤oddRows(mu)≤2ht. Consequently the first correction is at most 5kh and the second at most 6kh, so both lie in the displayed bands of width 7kh. The identity same_diagram_columns identifies oddRows with the squared column heights of the same actual diagram.

If two widths differ, spacing 128h and rU≥k make their first bands disjoint; differing heights make the second bands disjoint. Equality of the joint statistics therefore recovers both grid indices. The frame formulas then recover the two square-core statistics, and square_family recovers the core index. Zero padding preserves both statistics. The direct_list_fan affine formulas convert their joint injection into joint signed fan injection for the actual wordOfRows words.

The word and joint fan images each have exactly gridCount(U,h) gridCount(V,h) q^6 members, and this is a lower bound for the whole fixed-area word-fiber capacity. The grid counts satisfy U≤6144h gridCount(U,h) and V≤6144h gridCount(V,h), while h<1120q and k≤h². Multiplying these bounds gives c0 UVk²≤gridCount(U,h) gridCount(V,h) q^6≤capacity(u,v,k), with exactly c0=1/(6144² 1120⁶). This theorem concerns the large-area branch with actual area k.

**Definition 1.13 (The normalized integer area).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.normalizedArea`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.normalizedArea` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

normalizedArea(u,v,K)=toNat(min(K,uv−K)). The positive-area hypotheses establish nonnegativity before this conversion is used.

**Definition 1.14 (Indices in the original integer parameters).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.OriginalIndex`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.OriginalIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

OriginalIndex(u,v,K) is FrameIndex at normalizedArea and at the two minimum natural dimensions. Under the integer guards these dimensions equal U=min(u,k) and V=min(v,k).

**Definition 1.15 (The explicit word at the original area).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.originalWord`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.originalWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Construct sourceWord at the original natural dimensions and normalized area. If K equals that area, keep this word; otherwise reverse its letters. Under the full integer hypotheses, outer_reverse_contract proves that the latter word has area uv−k=K and preserves its joint signed moments.

**Definition 1.16 (The exact original family size).**

Lean statement: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.originalFamilySize`

*Formalization.* `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.originalFamilySize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At k=normalizedArea(u,v,K), originalFamilySize is gridCount(min(toNat(u),k),side(k)) times gridCount(min(toNat(v),k),side(k)) times q(level(k))^6. Each factor comes from the full computed index domain.

**Theorem 1.17 (Sparse capacity in the complete integer domain).**

$$\forall u \in \mathbb{Z}, \forall v \in \mathbb{Z}, \forall K \in \mathbb{Z}, (1 \leq u) \land (1 \leq v) \land (0 \leq K) \land (K \leq u \times v) \land (1 \leq \operatorname{min}\left(K, u \times v - K\right)) \land (4096 \times \operatorname{min}\left(K, u \times v - K\right) \leq (\operatorname{min}\left(u, v\right))^{2}) \implies (\operatorname{c0}\left(\right) \times \operatorname{min}\left(u, \operatorname{min}\left(K, u \times v - K\right)\right) \times \operatorname{min}\left(v, \operatorname{min}\left(K, u \times v - K\right)\right) \times (\operatorname{min}\left(K, u \times v - K\right))^{2} \leq \operatorname{capacity}\left(u, v, K\right)) \land (\operatorname{capacity}\left(u, v, K\right) \leq \operatorname{min}\left(u, \operatorname{min}\left(K, u \times v - K\right)\right) \times \operatorname{min}\left(v, \operatorname{min}\left(K, u \times v - K\right)\right) \times (\operatorname{min}\left(K, u \times v - K\right))^{2}) \land (4096 \leq \operatorname{min}\left(K, u \times v - K\right) \implies (\forall x \in \operatorname{OriginalIndex}\left(u, v, K\right), \operatorname{originalWord}\left(u, v, K, x\right) \in \operatorname{wordFiber}\left(u, v, K\right)) \land (\operatorname{Injective}\left(\operatorname{fun}\left(x:\operatorname{OriginalIndex}\left(u, v, K\right), \operatorname{Pair}\left(\operatorname{e}\left(\operatorname{G}\left(\operatorname{originalWord}\left(u, v, K, x\right)\right)\right), \operatorname{f}\left(\operatorname{G}\left(\operatorname{originalWord}\left(u, v, K, x\right)\right)\right)\right)\right)\right)) \land (\operatorname{Injective}\left(\operatorname{fun}\left(x:\operatorname{OriginalIndex}\left(u, v, K\right), \operatorname{originalWord}\left(u, v, K, x\right)\right)\right)) \land (\operatorname{ncard}\left(\operatorname{range}\left(\operatorname{fun}\left(x:\operatorname{OriginalIndex}\left(u, v, K\right), \operatorname{originalWord}\left(u, v, K, x\right)\right)\right)\right) = \operatorname{originalFamilySize}\left(u, v, K\right)) \land (\operatorname{ncard}\left(\operatorname{range}\left(\operatorname{fun}\left(x:\operatorname{OriginalIndex}\left(u, v, K\right), \operatorname{Pair}\left(\operatorname{e}\left(\operatorname{G}\left(\operatorname{originalWord}\left(u, v, K, x\right)\right)\right), \operatorname{f}\left(\operatorname{G}\left(\operatorname{originalWord}\left(u, v, K, x\right)\right)\right)\right)\right)\right)\right) = \operatorname{originalFamilySize}\left(u, v, K\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.sparse_joint_moment_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive integer u,v and every integer 0≤K≤uv, put k=min(K,uv−K), U=min(u,k), V=min(v,k). If k≥1 and 4096k≤min(u,v)², the capacity of the whole actual word fiber lies between c0 UVk² and UVk². Both original areas, every aspect ratio, perfect-square k and the full small positive range remain included.

For an actual word of area k, its sorted direct rows and the transpose of the same diagram have natural square sums. Both are at least k. Each row is bounded by U, so the first sum is at most Uk. For the same actual diagram, diagram_col_bound bounds each column height by v, and a double incidence count proves that the column heights sum to k. Each is therefore also at most k. Using same_diagram_columns and the transpose row lengths bounds the second sum by Vk. These two integer statistics from the same word belong to the joint rectangle [1,Uk] × [1,Vk]. The actual fan map sends this rectangle to an ambient set of at most UVk² points. Counting the ambient product proves an upper bound and does not assert simultaneous attainment of independently optimized marginals.

When 1≤k<4096, the sparse guard implies u,v≥k. The concrete sorted rows consist of one row k and v−1 zero rows. wordOfRows gives a nonempty actual word with the required counts and area, so the whole joint image has at least one point. The unchanged constant satisfies c0 UVk²≤c0 k⁴≤c0 4096⁴≤1. This directly constructs the small-area branch.

For k≥4096 the actual thick-frame family above gives the lower bound. Integer nonnegativity proves every toNat cast faithful. The existing joint_image_reverse equates the whole capacities at k and uv−k. Applying outer_reverse_contract to every constructed mathematical word preserves its joint moment pair and produces the original K. Thus originalWord has exactly the original u,v counts and area K, its joint map is injective, and its word and joint images each have exactly originalFamilySize members. These are source words, not claims about a physically free reversal operation or recovery of an arbitrary parenthesized tree.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.FrameIndex`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.OriginalIndex`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.c0`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.frameRows`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.grid`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.gridCount`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.level`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.normalizedArea`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.originalFamilySize`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.originalWord`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.residualArea`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.separated_frame_family`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.side`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.sourceRows`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.sourceWord`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.sparse_joint_moment_capacity`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SparseThickFrameFamily.thickness`
- Dependency: [D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore](PrescribedAreaSquareWordCore.md)
