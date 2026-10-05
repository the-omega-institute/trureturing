# Tight Palindromic Factorizations

## Abstract

The signed-weight lower bound is attained precisely when the prefix can be reduced to zero through tight palindrome cuts.

**Theorem 1.1 (Equality is equivalent to a tight cut path).**

$$\forall n \in \mathbb{N},\; \operatorname{PL}\left(\operatorname{ofFn}\left(i:\operatorname{Fin}\left(n\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right) = \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{NatDiv}\left(n + 1, 2\right), \mathbb{Z}\right)\right) \Leftrightarrow \left(\exists cuts \in \operatorname{List}\left(\mathbb{N}\right),\; \operatorname{ite}\left(\operatorname{cons}\left(n, cuts\right) = [], \operatorname{none}, \operatorname{some}\left(\operatorname{List.getLast}\left(\operatorname{cons}\left(n, cuts\right)\right)\right)\right) = \operatorname{some}\left(0\right) \land \operatorname{IsChain}\left(\operatorname{cons}\left(n, cuts\right), s:\mathbb{N} \mapsto t:\mathbb{N} \mapsto \left(t < s \land \operatorname{Palindrome}\left(\operatorname{ofFn}\left(i:\operatorname{Fin}\left(\operatorname{NatSub}\left(s, t\right)\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(t + \operatorname{val}\left(i\right)\right)\right)\right)\right) \land \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{NatDiv}\left(s + 1, 2\right), \mathbb{Z}\right)\right) = \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{NatDiv}\left(t + 1, 2\right), \mathbb{Z}\right)\right) + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/TightFactorization.tight_factorization_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The list starts at the prefix endpoint n and ends at zero. Each successive pair decreases the endpoint, removes a nonempty palindromic suffix, and lowers the signed weight of the rounded half by exactly one. An optimal factorization supplies such a path when equality holds; conversely, a tight path constructs a factorization meeting the lower bound. NatSub denotes truncated natural subtraction and NatDiv denotes natural integer division. The last-option expression is none for an empty list and some(List.getLast(...)) otherwise; the nonempty proof argument is implicit.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/TightFactorization.tight_factorization_iff`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SignedCutLowerBound](SignedCutLowerBound.md)
