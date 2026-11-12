# Kimberling A371279/A371280: one fraction enumeration

## Abstract

Every rational in (0,1] occurs exactly once in Kimberling's ordered fraction enumeration.

All arithmetic is exact rational arithmetic. Write C(n) for cumulative(n), so C(0) is the source's U(1). Write b(n) for block(n), g(n) for generation(n), F(n) for flattenedPrefix(n), and T(i) for fraction(i). Natural numbers include zero; Occurs uses strictly positive generation and within-generation indices. T uses zero for the first flattened entry. The source's one-based flattened position is flatIndex+1.

**Definition 1.1 (The complete ordered pair list).**

$$\forall s: \operatorname{List}\left(\mathbb{Q}\right), \operatorname{pairList}\left(s\right) = \operatorname{flatMap}\left(x \mapsto \operatorname{map}\left(y \mapsto \frac{x}{1 + y}, s\right), s\right)$$

*Formalization.* `D5/S3/Arith/CounterSequences/KimberlingA371279.pairList` (`✓ std3`).

*Citation.* Clark Kimberling; Peter J. C. Moses (2024). *OEIS A371279 and A371280: a first-retention enumeration of positive rationals at most one*. URL: <https://oeis.org/A371279>.

*Commentary.*

flatMap visits x in list order, then map visits every y in that same list order. Thus the numerator index is outermost and diagonal pairs are included. No final-generation restriction is imposed.

**Definition 1.2 (Cumulative lists and new suffixes).**

$$(\operatorname{C}\left(0\right) = [1]) \land (\forall n: \mathbb{N}, \operatorname{C}\left(n + 1\right) = \operatorname{nextList}\left(\operatorname{C}\left(n\right)\right))$$

*Formalization.* `D5/S3/Arith/CounterSequences/KimberlingA371279.cumulative` (`✓ std3`).

*Citation.* Clark Kimberling; Peter J. C. Moses (2024). *OEIS A371279 and A371280: a first-retention enumeration of positive rationals at most one*. URL: <https://oeis.org/A371279>.

*Commentary.*

freshTail(xs) is firstRetention of pairList(xs) filtered by absence from xs. nextList(xs) is xs concatenated with this suffix. firstRetention scans from left to right, keeping an entry exactly when its rational value has not already been seen. The proof identifies that scan with Lean's eraseDups. Lean's last-retention dedup is not used.

**Definition 1.3 (Positive generation numbers).**

$$(\operatorname{g}\left(0\right) = []) \land (\operatorname{b}\left(0\right) = [1]) \land (\forall n: \mathbb{N}, (\operatorname{g}\left(n + 1\right) = \operatorname{b}\left(n\right)) \land (\operatorname{b}\left(n + 1\right) = \operatorname{freshTail}\left(\operatorname{C}\left(n\right)\right)))$$

*Formalization.* `D5/S3/Arith/CounterSequences/KimberlingA371279.generation` (`✓ std3`).

*Citation.* Clark Kimberling; Peter J. C. Moses (2024). *OEIS A371279 and A371280: a first-retention enumeration of positive rationals at most one*. URL: <https://oeis.org/A371279>.

*Commentary.*

The empty generation zero is only an indexing convention and supplies no source positions. The first block is the seed; subsequent blocks are precisely the newly appended suffixes.

**Definition 1.4 (Ordered finite flattening).**

$$\forall n: \mathbb{N}, \operatorname{F}\left(n\right) = \operatorname{flatMap}\left(\operatorname{b}, \operatorname{range}\left(n\right)\right)$$

*Formalization.* `D5/S3/Arith/CounterSequences/KimberlingA371279.flattenedPrefix` (`✓ std3`).

*Citation.* Clark Kimberling; Peter J. C. Moses (2024). *OEIS A371279 and A371280: a first-retention enumeration of positive rationals at most one*. URL: <https://oeis.org/A371279>.

*Commentary.*

range(n) lists 0 through n-1 in increasing order. flatMap concatenates the corresponding generation blocks without reordering their entries.

**Definition 1.5 (Valid positive positions).**

$$\forall r: \mathbb{Q}, \forall n: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{Occurs}\left(r, (n,k)\right) \iff (0 < n) \land (0 < k) \land (k \le \operatorname{length}\left(\operatorname{g}\left(n\right)\right)) \land (\operatorname{lookup}\left(\operatorname{g}\left(n\right), k - 1\right) = \operatorname{some}\left(r\right))$$

*Formalization.* `D5/S3/Arith/CounterSequences/KimberlingA371279.Occurs` (`✓ std3`).

*Citation.* Clark Kimberling; Peter J. C. Moses (2024). *OEIS A371279 and A371280: a first-retention enumeration of positive rationals at most one*. URL: <https://oeis.org/A371279>.

*Commentary.*

lookup is optional zero-based list lookup. The length bound and positive index exclude default or out-of-range readings, including empty generations.

**Definition 1.6 (The flattened index of a generation position).**

$$\forall n: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{flatIndex}\left((n,k)\right) = \operatorname{length}\left(\operatorname{F}\left(n - 1\right)\right) + (k - 1)$$

*Formalization.* `D5/S3/Arith/CounterSequences/KimberlingA371279.flatIndex` (`✓ std3`).

*Citation.* Clark Kimberling; Peter J. C. Moses (2024). *OEIS A371279 and A371280: a first-retention enumeration of positive rationals at most one*. URL: <https://oeis.org/A371279>.

*Commentary.*

The length of F(n-1) counts all earlier entries; k-1 is the within-generation offset.

**Theorem 1.7 (Literal source update).**

$$\forall s: \operatorname{List}\left(\mathbb{Q}\right), (\operatorname{Nodup}\left(s\right)) \implies (\operatorname{nextList}\left(s\right) = \operatorname{eraseDups}\left(\operatorname{append}\left(s, \operatorname{pairList}\left(s\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CounterSequences/KimberlingA371279.source_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Clark Kimberling; Peter J. C. Moses (2024). *OEIS A371279 and A371280: a first-retention enumeration of positive rationals at most one*. URL: <https://oeis.org/A371279>.

*Commentary.*

For every duplicate-free old list, the prefix-plus-suffix construction equals first-occurrence retention of the entire old list followed by the complete ordered pair list. The old prefix remains in its original order.

Strong induction on q simultaneously covers every p/q with 1<=p<=q. The seed handles p=q. If p<q and 2p<=q, the permitted diagonal pair at p/(q-p) produces p/q. If 2p>q, the pair (1,(q-p)/p) produces p/q. Both inputs are moved into one common cumulative list by nesting. The canonical rational numerator and positive denominator reduce an arbitrary interval rational to this induction. Different generation blocks are disjoint because each new suffix excludes the entire old prefix. Each block is duplicate-free, so uniqueness includes its within-generation index.

**Theorem 1.8 (The complete source event and array bridge).**

$$(\forall n: \mathbb{N}, \operatorname{C}\left(n + 1\right) = \operatorname{eraseDups}\left(\operatorname{append}\left(\operatorname{C}\left(n\right), \operatorname{pairList}\left(\operatorname{C}\left(n\right)\right)\right)\right)) \land (\forall n: \mathbb{N}, \operatorname{C}\left(n\right) = \operatorname{F}\left(n + 1\right)) \land (\forall n: \mathbb{N}, \forall r: \mathbb{Q}, (r \in \operatorname{C}\left(n\right)) \implies ((0 < r) \land (r \le 1))) \land (\forall r: \mathbb{Q}, ((0 < r) \land (r \le 1)) \implies (\exists ! p: \mathbb{N} \times \mathbb{N}, \operatorname{Occurs}\left(r, p\right))) \land (\forall t: \mathbb{N}, \exists n: \mathbb{N}, t < \operatorname{length}\left(\operatorname{F}\left(n\right)\right)) \land (\forall n: \mathbb{N}, \forall i: \mathbb{N}, (i < \operatorname{length}\left(\operatorname{F}\left(n\right)\right)) \implies (\operatorname{lookup}\left(\operatorname{F}\left(n\right), i\right) = \operatorname{some}\left(\operatorname{T}\left(i\right)\right))) \land (\forall r: \mathbb{Q}, \forall p: \mathbb{N} \times \mathbb{N}, (\operatorname{Occurs}\left(r, p\right)) \implies (\operatorname{T}\left(\operatorname{flatIndex}\left(p\right)\right) = r)) \land (\forall t: \mathbb{N}, \exists ! p: \mathbb{N} \times \mathbb{N}, (\operatorname{Occurs}\left(\operatorname{T}\left(t\right), p\right)) \land (\operatorname{flatIndex}\left(p\right) = t)) \land (\forall i: \mathbb{N}, \forall j: \mathbb{N}, (\operatorname{T}\left(i\right) = \operatorname{T}\left(j\right)) \implies (i = j)) \land (\forall i: \mathbb{N}, ((0 < \operatorname{T}\left(i\right)) \land (\operatorname{T}\left(i\right) \le 1)) \land (0 < \operatorname{den}\left(i\right)) \land (\operatorname{Coprime}\left(\operatorname{natAbs}\left(\operatorname{num}\left(i\right)\right), \operatorname{den}\left(i\right)\right)) \land (\operatorname{T}\left(i\right) = \frac{\operatorname{num}\left(i\right)}{\operatorname{den}\left(i\right)}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CounterSequences/KimberlingA371279.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a371279-a371280-rational-enumeration` (proved) by `D5/S3/Arith/CounterSequences/KimberlingA371279.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a371279-a371280-rational-enumeration","declaration_gid":"D5/S3/Arith/CounterSequences/KimberlingA371279.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Clark Kimberling; Peter J. C. Moses (2024). *OEIS A371279 and A371280: a first-retention enumeration of positive rationals at most one*. URL: <https://oeis.org/A371279>.

*Commentary.*

The ten conjuncts below give the literal update, finite flattening, interval invariant, exactly one positive generation/index pair for every target rational, unbounded prefixes, consistent infinite readings, the position-to-flat bridge, a unique owner for every flat index, injectivity of T, and its canonical reduced coordinates. num(i)=numerator(i)=(T(i)).num and den(i)=denominator(i)=(T(i)).den. The arrays A371279 and A371280 are these two coordinate records of the same T; neither coordinate is claimed individually injective. This does not validate published finite array digits or execute Mathematica. The denominator-induction route is attributed to the supplied GPT Pro search candidate; no independent-discovery or research-difficulty claim is made.

## References

- Truth anchor: `D5/S3/Arith/CounterSequences/KimberlingA371279.Occurs`
- Truth anchor: `D5/S3/Arith/CounterSequences/KimberlingA371279.cumulative`
- Truth anchor: `D5/S3/Arith/CounterSequences/KimberlingA371279.flatIndex`
- Truth anchor: `D5/S3/Arith/CounterSequences/KimberlingA371279.flattenedPrefix`
- Truth anchor: `D5/S3/Arith/CounterSequences/KimberlingA371279.generation`
- Truth anchor: `D5/S3/Arith/CounterSequences/KimberlingA371279.pairList`
- Truth anchor: `D5/S3/Arith/CounterSequences/KimberlingA371279.result`
- Truth anchor: `D5/S3/Arith/CounterSequences/KimberlingA371279.source_update`
