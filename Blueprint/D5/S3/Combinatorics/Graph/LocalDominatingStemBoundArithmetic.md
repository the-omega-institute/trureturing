# Replicated dominating-set averages

## Abstract

A quadratic binomial estimate controls the counting bases and averages of replicated graph families.

**Theorem 1.1 (Finite replication obstruction).**

$$\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \forall h \in \mathrm{Nat},\; 0 < b \Rightarrow \left(b < a \Rightarrow \left(\neg \operatorname{pow}\left(\operatorname{rat}\left(a\right), 4 \cdot h \cdot \operatorname{pow}\left(b, 2\right) + 2\right) \le \operatorname{pow}\left(\operatorname{rat}\left(b\right), 4 \cdot h \cdot \operatorname{pow}\left(b, 2\right) + 2\right) \cdot \left(1 + 2 \cdot \operatorname{rat}\left(4 \cdot h \cdot \operatorname{pow}\left(b, 2\right) + 2\right) \cdot \operatorname{rat}\left(h\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic.replication_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write r=4hb²+2. For a>b≥1, the ratio a/b is at least 1+1/b. Its r-th power is at least 1+r/b+r(r−1)/(2b²), whose excess above 1+2rh is r/b+r/(2b²)>0.

**Theorem 1.2 (Comparison of counting bases).**

$$\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \forall h \in \mathrm{Nat},\; 0 < b \Rightarrow \left(\left(\forall r \in \mathrm{Nat},\; \operatorname{pow}\left(\operatorname{rat}\left(a\right), r\right) \le \operatorname{pow}\left(\operatorname{rat}\left(b\right), r\right) \cdot \left(1 + 2 \cdot \operatorname{rat}\left(r\right) \cdot \operatorname{rat}\left(h\right)\right)\right) \Rightarrow a \le b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic.counting_base_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a^r≤b^r(1+2rh) for every nonnegative integer r and b>0, then a≤b. The displayed finite replication count excludes the opposite inequality.

**Theorem 1.3 (Strict inequality for unequal families).**

$$\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; \forall h \in \mathrm{Nat},\; \forall alpha \in \mathrm{Rat},\; \forall beta \in \mathrm{Rat},\; 0 < b \Rightarrow \left(b < a \Rightarrow \left(0 \le beta \Rightarrow \left(\left(\forall r \in \mathrm{Nat},\; \operatorname{pow}\left(\operatorname{rat}\left(a\right), r\right) \cdot \left(1 + 6 \cdot \operatorname{rat}\left(r\right) \cdot \left(alpha - \frac{2 \cdot \operatorname{rat}\left(h\right)}{3}\right)\right) \le \operatorname{pow}\left(\operatorname{rat}\left(b\right), r\right) \cdot \left(1 + 3 \cdot \operatorname{rat}\left(r\right) \cdot \left(\frac{2 \cdot \operatorname{rat}\left(h\right)}{3} - beta\right)\right)\right) \Rightarrow alpha < \frac{2 \cdot \operatorname{rat}\left(h\right)}{3}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic.replicated_mean_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose β≥0 and the replicated global bounds hold. If α≥2h/3, their left factors are at least one, and their right factors are at most 1+2rh. This contradicts a>b, so α<2h/3.

**Theorem 1.4 (Bound and counting equality for relaxed means).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic.relaxed_mean_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic.relaxed_mean_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For naturals a,b,h and rational means α,β, assume b>0, b≤a, 0≤β≤2h/3, a=b implies α=β, and the replicated global inequalities hold for every nonnegative integer r. Then α≤2h/3, and α=2h/3 implies a=b.

**Theorem 1.5 (Numerical bound and equality in the stem split).**

$$\forall n \in \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; \forall h \in \mathrm{Nat},\; \forall alpha \in \mathrm{Rat},\; n = h + l + 1 \Rightarrow \left(1 \le l \Rightarrow \left(alpha \le \frac{2 \cdot \operatorname{rat}\left(h\right)}{3} \Rightarrow \left(1 + \frac{\operatorname{rat}\left(l\right)}{2} + alpha \le \frac{4 \cdot \operatorname{rat}\left(n\right) + 1}{6} \land \left(1 + \frac{\operatorname{rat}\left(l\right)}{2} + alpha = \frac{4 \cdot \operatorname{rat}\left(n\right) + 1}{6} \Leftrightarrow \left(l = 1 \land alpha = \frac{2 \cdot \operatorname{rat}\left(h\right)}{3}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic.stem_split_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n=h+l+1, l≥1 and α≤2h/3, the stem-conditioned mean 1+l/2+α is at most (4n+1)/6. Equality holds exactly when l=1 and α=2h/3.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic.counting_base_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic.relaxed_mean_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic.replicated_mean_lt`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic.replication_obstruction`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundArithmetic.stem_split_bound`
