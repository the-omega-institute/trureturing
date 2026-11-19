# Actual Lyndon factors and elementary transport

## Abstract

A suffix-minimum scan computes distinct contiguous Lyndon factor strings.

All scan statements quantify over an arbitrary linearly ordered alphabet A and finite lists. Lexicographic order treats a proper prefix as smaller. The scan is related to the original refutation's finite-index factor, occurrence and distinct-count definitions. The supplied Ma–Zhang manuscript gives the suffix-minimum scan argument. The elementary morphism is the classical lambda(a)=a, lambda(b)=ab; its proof uses the existing actual two-factor standard factorization. Richomme's Lyndon-morphism theory is prior literature; no novelty or global priority is asserted.

**Definition 1.1 (Minimum nonempty suffix).**

$$\operatorname{leastSuffix}\left(w\right) = \operatorname{min}\left(\operatorname{nonemptySuffixes}\left(w\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/LyndonFactorTransport.leastSuffix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

For nonempty w this recursively takes the smaller of w and the minimum nonempty suffix of its tail. On the empty input it returns the empty sentinel; that sentinel is never compared in the acceptance test.

**Definition 1.2 (Scan a fixed right endpoint).**

$$\operatorname{suffixScan}\left(w\right) = \operatorname{recordMinima}\left(\operatorname{nonemptySuffixesShortestFirst}\left(w\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/LyndonFactorTransport.suffixScan` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

Start with the last letter. Prepend successively longer suffixes; accept exactly when a candidate is strictly less than the minimum already seen. This computes strings by comparisons and never tests IsLyndon.

**Definition 1.3 (Identify equal accepted strings).**

$$\operatorname{factorScan}\left(w\right) = \operatorname{toFinset}\left(\operatorname{flatMap}\left(\operatorname{suffixScan}, \operatorname{inits}\left(w\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/LyndonFactorTransport.factorScan` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

Run suffixScan on every prefix, including the harmless empty prefix, then deduplicate the resulting strings. Thus all right endpoints are covered and repeated occurrences count once.

**Theorem 1.4 (Exact suffix scan).**

$$\forall u w,u\in\operatorname{suffixScan}\left(w\right)\iff\operatorname{IsLyndon}\left(u\right)\land\operatorname{IsSuffix}\left(u, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonFactorTransport.mem_suffixScan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

For every u,w : List A, scan membership is equivalent to u being a Lyndon suffix of w. Induction maintains the minimum of every proper nonempty suffix, and the existing rotation/suffix equivalence supplies precisely the acceptance condition.

**Theorem 1.5 (Exact contiguous factor scan).**

$$\forall u w,u\in\operatorname{factorScan}\left(w\right)\iff\operatorname{IsLyndon}\left(u\right)\land\operatorname{IsInfix}\left(u, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonFactorTransport.mem_factorScan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

For every u,w : List A, membership is exactly Lyndonness and contiguous occurrence. A substring is a suffix of a prefix. Empty strings are excluded by Lyndonness, while letters and a Lyndon whole word are included.

**Theorem 1.6 (The original occurrence image).**

$$\forall \sigma: \mathbb{N}, \forall n: \mathbb{N}, \forall w: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(\sigma\right), \operatorname{factorScan}\left(\operatorname{List.map}\left(w, \operatorname{List.finRange}\left(n\right)\right)\right) = \operatorname{Finset.image}\left((p: \mathbb{N}\times\mathbb{N} \mapsto \operatorname{factor}\left(w, p.1, p.2\right)), \operatorname{lyndonOccurrences}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonFactorTransport.factorScan_eq_occurrence_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

For every sigma,n and w : Fin n -> Fin sigma, the scan set equals the image sending each valid pair (i,l) in lyndonOccurrences w to factor w i l. The proof reconstructs a valid slice from an arbitrary contiguous occurrence; its nonemptiness gives l>=1 and its enclosing word gives i+l<=n.

**Theorem 1.7 (The original distinct count).**

$$\forall \sigma: \mathbb{N}, \forall n: \mathbb{N}, \forall w: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(\sigma\right), \operatorname{distinctLyndon}\left(w\right) = \operatorname{Finset.card}\left(\operatorname{factorScan}\left(\operatorname{List.map}\left(w, \operatorname{List.finRange}\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonFactorTransport.distinctLyndon_eq_scan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

The original distinctLyndon count is exactly the cardinality of the scan set. This is an equality of the actual factor objects, with no count recurrence or occurrence-count replacement.

**Definition 1.8 (Letter-image morphism).**

$$\operatorname{mapWord}\left(f, w\right) = \operatorname{List.flatMap}\left(f, w\right)$$

*Formalization.* `D5/S1/Words/Complexity/LyndonFactorTransport.mapWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

For f : Fin 2 -> List (Fin 2), concatenate the letter images in their input order.

**Definition 1.9 (The elementary left morphism).**

$$\operatorname{elementaryLeft}\left(a\right) = \operatorname{lambda}\left(a\right)$$

*Formalization.* `D5/S1/Words/Complexity/LyndonFactorTransport.elementaryLeft` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

The smaller letter 0 maps to [0], and the larger letter 1 maps to [0,1].

**Theorem 1.10 (Actual elementary preservation and reflection).**

$$\forall w,\operatorname{IsLyndon}\left(\operatorname{mapWord}\left(\operatorname{elementaryLeft}, w\right)\right)\iff\operatorname{IsLyndon}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonFactorTransport.elementaryLeft_lyndon_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

For every binary list w, including letters and the empty list, lambda(w) is Lyndon iff w is Lyndon. Preservation inducts through the actual standard left and right Lyndon factors; reflection uses strict order preservation and actual concatenated images of rotations. This does not assert a factor-set identity on the wider domain.

**Theorem 1.11 (An additional factor outside the morphism image).**

$$\forall w,1\in w\Rightarrow\operatorname{card}\left(\operatorname{factorScan}\left(w\right)\right)+1\leq\operatorname{card}\left(\operatorname{factorScan}\left(\operatorname{mapWord}\left(\operatorname{elementaryLeft}, w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/LyndonFactorTransport.elementaryLeft_factor_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Amy Glen, Jamie Simpson, and W. F. Smyth (2017). *Counting Lyndon factors*. DOI: [10.37236/6915](https://doi.org/10.37236/6915). URL: <https://arxiv.org/abs/1701.00928v1>.

*Commentary.*

For every binary list w containing the letter 1, the lambda image has at least one more distinct Lyndon factor. Every input Lyndon factor maps injectively to an actual output factor, while [1] occurs and is outside the image because every nonempty lambda image starts with 0. This is a proved lower bound, not the still-open exact factor-set identity or exact count increment.

Open boundaries: general block factor sets/counts, rho and arbitrary composite transport, original h and its factor-count +8 identity, and exact nested sets remain unproved here. Scan correctness does not certify the retained 220-row data, CF/word correspondence, Fibonacci family, arbitrary-alphabet minima, or the 9082 comparison. Saari's equality/length obligations, GSS's specific Christoffel domain, and the unavailable Glen2018 proof boundary remain unchanged.

## References

- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorTransport.distinctLyndon_eq_scan`
- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorTransport.elementaryLeft`
- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorTransport.elementaryLeft_factor_growth`
- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorTransport.elementaryLeft_lyndon_iff`
- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorTransport.factorScan`
- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorTransport.factorScan_eq_occurrence_image`
- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorTransport.leastSuffix`
- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorTransport.mapWord`
- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorTransport.mem_factorScan`
- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorTransport.mem_suffixScan`
- Truth anchor: `D5/S1/Words/Complexity/LyndonFactorTransport.suffixScan`
- Dependency: [D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization](LyndonBrackets/LyndonStandardFactorization.md)
- Dependency: [D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation](LyndonFactorChristoffelMinimumRefutation.md)
