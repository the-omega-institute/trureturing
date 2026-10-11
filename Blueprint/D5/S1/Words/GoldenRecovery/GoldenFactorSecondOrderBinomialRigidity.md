# Second-order binomial recovery of golden factors

## Abstract

At a fixed length, the true count and scattered true-before-false count determine a consecutive golden factor. Prefix counts compare in one orientation, so equality of their total area forces equality of every letter.

Write W(n,i) for goldenFactor(n,i), the list of goldenWord(i+k) for zero through n minus one, and R(i,m) for goldenWindowTrueCount(i,m). Both indices and lengths are arbitrary naturals. The count R(i,m) is the natural number of true letters in that prefix.

**Definition 1.1 (The sum of all prefix counts).**

$$\forall i \in Nat,\; \forall n \in Nat,\; \operatorname{A}\left(i, n\right) = \sum_{m\in \operatorname{range}\left(n + 1\right)}\operatorname{R}\left(i, m\right)$$

*Formalization.* `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.goldenPrefixArea` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The area A(i,n) abbreviates goldenPrefixArea(i,n). It includes every prefix length from zero through n, so the empty prefix contributes zero.

**Definition 1.2 (Scattered true-before-false pairs).**

$$\forall i \in Nat,\; \forall n \in Nat,\; \operatorname{B}\left(i, n\right) = \sum_{k\in \operatorname{range}\left(n\right)}\operatorname{if}\left(\operatorname{goldenWord}\left(i + k\right) = true, 0, \operatorname{R}\left(i, k\right)\right)$$

*Formalization.* `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.goldenTrueFalseCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B(i,n) abbreviates goldenTrueFalseCount(i,n). At each false letter in the window, add the number of true letters in the preceding prefix. A true letter contributes zero, and intervening letters are unrestricted.

**Definition 1.3 (The reduced binomial profile).**

$$\forall n \in Nat,\; \forall i \in Nat,\; \operatorname{goldenBinomialProfile}\left(n, i\right) = (\operatorname{R}\left(i, n\right),\operatorname{B}\left(i, n\right))$$

*Formalization.* `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.goldenBinomialProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The profile records the final true count and the scattered-pair count, in that order. The length n is a fixed parameter, rather than a third coordinate.

**Theorem 1.4 (A common order for every prefix).**

$$\forall i \in Nat,\; \forall j \in Nat,\; \left(\forall m \in Nat,\; \operatorname{R}\left(i, m\right) \le \operatorname{R}\left(j, m\right)\right) \lor \left(\forall m \in Nat,\; \operatorname{R}\left(j, m\right) \le \operatorname{R}\left(i, m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.golden_prefix_counts_comparable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Beatty formula writes the integer cast of R(i,m) as floor(fract((i+1)/phi)+m/phi), with phi the golden ratio. Ordering the two intercept phases orders all their prefix counts in the same direction, simultaneously for every natural m.

**Theorem 1.5 (Prefix area determines the word).**

$$\forall n \in Nat,\; \forall i \in Nat,\; \forall j \in Nat,\; \operatorname{A}\left(i, n\right) = \operatorname{A}\left(j, n\right) \Rightarrow \operatorname{W}\left(n, i\right) = \operatorname{W}\left(n, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.golden_factor_eq_of_prefix_area_eq` (`✓ std3`). ∎

*Citation.* Michel Rigo; Pavel Salimov (2015). *Another generalization of abelian equivalence: Binomial complexity of infinite words*. DOI: [10.1016/j.tcs.2015.07.025](https://doi.org/10.1016/j.tcs.2015.07.025). URL: <https://orbi.uliege.be/handle/2268/178703>.

*Commentary.*

For a fixed n, comparable nonnegative summands with equal total area are equal at every prefix length up to n. Successive prefix-count differences are the true-letter indicators, so equality of the prefixes recovers every letter of W(n,i). No positivity assumption on n is required.

**Theorem 1.6 (The exact binomial area identity).**

$$\forall i \in Nat,\; \forall n \in Nat,\; 2 \cdot \operatorname{A}\left(i, n\right) = 2 \cdot \operatorname{B}\left(i, n\right) + \operatorname{R}\left(i, n\right) \cdot \left(\operatorname{R}\left(i, n\right) + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.golden_prefix_area_binomial_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Appending false adds the old true count to B and leaves the final true count unchanged. Appending true raises the true count by one and adds no pair. These two cases give the integral identity by induction; using twice the area avoids division.

**Theorem 1.7 (Two counts recover a fixed-length factor).**

$$\forall n \in Nat,\; \forall i \in Nat,\; \forall j \in Nat,\; \operatorname{R}\left(i, n\right) = \operatorname{R}\left(j, n\right) \Rightarrow \left(\operatorname{B}\left(i, n\right) = \operatorname{B}\left(j, n\right) \Rightarrow \operatorname{W}\left(n, i\right) = \operatorname{W}\left(n, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.golden_factor_eq_of_second_order_counts` (`✓ std3`). ∎

*Citation.* Michel Rigo; Pavel Salimov (2015). *Another generalization of abelian equivalence: Binomial complexity of infinite words*. DOI: [10.1016/j.tcs.2015.07.025](https://doi.org/10.1016/j.tcs.2015.07.025). URL: <https://orbi.uliege.be/handle/2268/178703>.

*Commentary.*

Equal true counts and equal scattered-pair counts give equal prefix areas by the identity, and hence equal words. The conclusion recovers word content, without identifying the absolute occurrence indices i and j.

**Theorem 1.8 (Exactly the same observation fibers).**

$$\forall n \in Nat,\; \forall i \in Nat,\; \forall j \in Nat,\; \operatorname{W}\left(n, i\right) = \operatorname{W}\left(n, j\right) \Leftrightarrow \operatorname{goldenBinomialProfile}\left(n, i\right) = \operatorname{goldenBinomialProfile}\left(n, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.golden_factor_eq_iff_second_order_profile_eq` (`✓ std3`). ∎

*Citation.* Michel Rigo; Pavel Salimov (2015). *Another generalization of abelian equivalence: Binomial complexity of infinite words*. DOI: [10.1016/j.tcs.2015.07.025](https://doi.org/10.1016/j.tcs.2015.07.025). URL: <https://orbi.uliege.be/handle/2268/178703>.

*Commentary.*

Conversely, equal words have equal counts in every prefix and equal letters at every position, hence equal B. Thus word equality is equivalent to profile equality at each specified length. For n equal to zero, every word is empty and every profile is (0,0). Pure-letter windows require no separate guard.

## References

- Truth anchor: `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.goldenBinomialProfile`
- Truth anchor: `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.goldenPrefixArea`
- Truth anchor: `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.goldenTrueFalseCount`
- Truth anchor: `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.golden_factor_eq_iff_second_order_profile_eq`
- Truth anchor: `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.golden_factor_eq_of_prefix_area_eq`
- Truth anchor: `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.golden_factor_eq_of_second_order_counts`
- Truth anchor: `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.golden_prefix_area_binomial_identity`
- Truth anchor: `D5/S1/Words/GoldenRecovery/GoldenFactorSecondOrderBinomialRigidity.golden_prefix_counts_comparable`
