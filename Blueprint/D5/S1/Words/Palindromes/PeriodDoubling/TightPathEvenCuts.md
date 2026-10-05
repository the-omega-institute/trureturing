# At Most One Tight Even Cut

## Abstract

A tight palindrome-cut path has at most one even-length deletion.

**Theorem 1.1 (The path obstruction).**

$$\forall n \in \mathbb{N},\; \forall cuts \in \operatorname{List}\left(\mathbb{N}\right),\; \left(\operatorname{classS}\left(n\right) \land \operatorname{IsChain}\left(\operatorname{cons}\left(n, cuts\right), s:\mathbb{N} \mapsto t:\mathbb{N} \mapsto \left(t < s \land \operatorname{Palindrome}\left(\operatorname{ofFn}\left(i:\operatorname{Fin}\left(\operatorname{Nat.sub}\left(s, t\right)\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(t + \operatorname{val}\left(i\right)\right)\right)\right)\right) \land \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(s + 1, 2\right), \mathbb{Z}\right)\right) = \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(t + 1, 2\right), \mathbb{Z}\right)\right) + 1\right)\right) \Rightarrow \operatorname{length}\left(\operatorname{filter}\left(e:\mathbb{N} \times \mathbb{N} \mapsto (\operatorname{mod}\left(\operatorname{fst}\left(e\right), 2\right) == \operatorname{mod}\left(\operatorname{snd}\left(e\right), 2\right)), \operatorname{zip}\left(\operatorname{cons}\left(n, cuts\right), cuts\right)\right)\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/TightPathEvenCuts.tight_path_at_most_one_even_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The path is any finite descending list of literal tight palindrome cuts beginning in class S. Its even cuts are exactly the pairs with equal endpoint parity. An even palindrome has length two. Signed-weight arithmetic and the source letters force a tight even cut to start at an odd integer at least five with odd rounded half; its successor has positive dyadic valuation. Class preservation and lowest-position monotonicity keep that valuation positive until zero, excluding any further even cut. Induction counts the exceptional first even cut. The statement does not require the path to end at zero. div denotes natural integer quotient and Nat.sub denotes truncated natural subtraction.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/TightPathEvenCuts.tight_path_at_most_one_even_cut`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/TightCutCharge](TightCutCharge.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/TightCutLowestPosition](TightCutLowestPosition.md)
