# Odd Cuts in Even Tight Paths

## Abstract

Every cut in an even tight path from an even endpoint to zero has odd length.

**Theorem 1.1 (The path obstruction).**

$$\forall n \in \mathbb{N},\; \forall cuts \in \operatorname{List}\left(\mathbb{N}\right),\; \left(\left(\left(\left(\operatorname{classS}\left(n\right) \land \operatorname{mod}\left(n, 2\right) = 0\right) \land \operatorname{mod}\left(\operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(n + 1, 2\right), \mathbb{Z}\right)\right), 2\right) = 0\right) \land \operatorname{ite}\left(\operatorname{cons}\left(n, cuts\right) = [], \operatorname{none}, \operatorname{some}\left(\operatorname{List.getLast}\left(\operatorname{cons}\left(n, cuts\right)\right)\right)\right) = \operatorname{some}\left(0\right)\right) \land \operatorname{IsChain}\left(\operatorname{cons}\left(n, cuts\right), s:\mathbb{N} \mapsto t:\mathbb{N} \mapsto \left(t < s \land \operatorname{Palindrome}\left(\operatorname{ofFn}\left(i:\operatorname{Fin}\left(\operatorname{NatSub}\left(s, t\right)\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(t + \operatorname{val}\left(i\right)\right)\right)\right)\right) \land \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(s + 1, 2\right), \mathbb{Z}\right)\right) = \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(t + 1, 2\right), \mathbb{Z}\right)\right) + 1\right)\right) \Rightarrow \operatorname{IsChain}\left(\operatorname{cons}\left(n, cuts\right), s:\mathbb{N} \mapsto t:\mathbb{N} \mapsto \operatorname{mod}\left(s, 2\right) \ne \operatorname{mod}\left(t, 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/EvenTightPaths.even_tight_path_has_only_odd_cuts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial endpoint belongs to class S and is even, and its rounded-half signed weight is even. The descending path ends at zero and every cut is a literal palindrome whose signed weight drops by one. Induction makes the number of cuts equal to the initial signed weight and balances endpoint parity with the count of equal-parity edges. The one-even-cut bound then forces that count to zero, so all endpoint parities differ. div denotes natural integer quotient and NatSub denotes truncated natural subtraction. The last-option expression is none for an empty list and some(List.getLast(...)) otherwise; the nonempty proof argument is implicit.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/EvenTightPaths.even_tight_path_has_only_odd_cuts`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/TightPathEvenCuts](TightPathEvenCuts.md)
