# BalaA363412Valuation

## Abstract

Integer quadratic products and Bala's valuation conjectures.

**Definition 1.1 (The paired valuation conjecture).**

$$\operatorname{claim} = \left(\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\operatorname{padicValInt}\left(3, \operatorname{BalaA363411}.\operatorname{b}\left(3 \cdot n\right)\right) = \operatorname{padicValInt}\left(3, \operatorname{BalaA363411}.\operatorname{b}\left(3 \cdot n - 1\right)\right))\right)$$

*Formalization.* `D5/S3/Arith/Congruence/BalaA363412Valuation.claim` (`✓ std3`).

*Citation.* P. Bala (2023). *OEIS A363411 and A363412 — quadratic integer product coordinates*. URL: <https://oeis.org/A363411>.

*Commentary.*

OEIS A363412, FORMULA (revision 19, no page): "Conjectures: 3 does not divide a(3*n+1) for all n; the 3-adic valuation v_3(a(3*n)) = v_3(a(3*n-1)) for all n." The second clause starts at n=1 so both source indices are nonnegative. The subtraction 3n-1 is natural truncated subtraction. The source sequence is BalaA363411.b.

**Theorem 1.2 (The paired three-adic valuations agree).**

$$\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\operatorname{padicValInt}\left(3, \operatorname{BalaA363411}.\operatorname{b}\left(3 \cdot n\right)\right) = \operatorname{padicValInt}\left(3, \operatorname{BalaA363411}.\operatorname{b}\left(3 \cdot n - 1\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/BalaA363412Valuation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bala3634-paired-valuations` (proved) by `D5/S3/Arith/Congruence/BalaA363412Valuation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bala3634-paired-valuations","declaration_gid":"D5/S3/Arith/Congruence/BalaA363412Valuation.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* P. Bala (2023). *OEIS A363411 and A363412 — quadratic integer product coordinates*. URL: <https://oeis.org/A363411>.

*Commentary.*

At indices 3n and 3n-1, the reflection congruences express twice the imaginary coordinate as 3n times an integer prime to 3. For n at least one the factor 3n is nonzero. Multiplicativity of padicValInt removes the unit factors; both valuations equal padicValInt 3 (3n).

## References

- Truth anchor: `D5/S3/Arith/Congruence/BalaA363412Valuation.claim`
- Truth anchor: `D5/S3/Arith/Congruence/BalaA363412Valuation.result`
- Dependency: [D5/S3/Arith/Congruence/BalaA363412](BalaA363412.md)
