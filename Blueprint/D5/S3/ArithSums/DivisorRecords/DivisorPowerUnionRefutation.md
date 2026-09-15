# The A396596 Divisor-Power Union Refutation

## Abstract

A divisor-power record at exponent minus four refutes the highly-composite or deeply-composite union in OEIS A396596.

For N = 32125373280, exponent -4 yields a strict divisor-power record. Neither endpoint class contains N. The formulas preserve the preregistered natural and real domains.

**Definition 1.1 (Real powers of all positive divisors).**

$$\forall n \in \mathbb{N},\; \forall x \in \mathbb{R},\; \operatorname{DivisorPowerSum}\left(n, x\right) = \sum_{d \in \operatorname{divisors}\left(n\right)} (d : \mathbb{R})^{x}$$

*Formalization.* `D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.DivisorPowerSum` (`✓ std3`).

*Citation.* Hal M. Switkay (2026). *OEIS A396596: divisor-power records and the highly/deeply composite union conjecture*. URL: <https://oeis.org/search?q=id:A396596&fmt=text>.

*Commentary.*

For positive natural n, divisors(n) is the finite set of all positive natural divisors, including 1 and n. Each divisor is cast to the reals before taking its real power; the sum is real-valued. Lean's Nat.divisors at zero is empty.

**Definition 1.2 (Strict records against every positive predecessor).**

$$\forall n \in \mathbb{N},\; \forall x \in \mathbb{R},\; (\operatorname{StrictDivisorPowerRecord}\left(n, x\right)) \Leftrightarrow ((0 < n) \land (\forall m \in \mathbb{N},\; (0 < m) \Rightarrow ((m < n) \Rightarrow (\operatorname{DivisorPowerSum}\left(m, x\right) < \operatorname{DivisorPowerSum}\left(n, x\right)))))$$

*Formalization.* `D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.StrictDivisorPowerRecord` (`✓ std3`).

*Citation.* Hal M. Switkay (2026). *OEIS A396596: divisor-power records and the highly/deeply composite union conjecture*. URL: <https://oeis.org/search?q=id:A396596&fmt=text>.

*Commentary.*

One fixed real exponent must beat every smaller positive natural simultaneously. The candidate must be positive; for n = 1 the predecessor condition is empty. At exponent zero every divisor contributes one, so a record is highly composite.

**Definition 1.3 (The exact universal union conjecture).**

$$(claim) \Leftrightarrow (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow ((\exists x \in \mathbb{R},\; (x \le 0) \land (\operatorname{StrictDivisorPowerRecord}\left(n, x\right))) \Leftrightarrow ((\operatorname{StrictDivisorPowerRecord}\left(n, 0\right)) \lor (\exists B \in \mathbb{R},\; (B < 0) \land (\forall x \in \mathbb{R},\; (x \le B) \Rightarrow (\operatorname{StrictDivisorPowerRecord}\left(n, x\right)))))))$$

*Formalization.* `D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.claim` (`✓ std3`).

*Citation.* Hal M. Switkay (2026). *OEIS A396596: divisor-power records and the highly/deeply composite union conjecture*. URL: <https://oeis.org/search?q=id:A396596&fmt=text>.

*Commentary.*

Switkay's selected sentence is: We conjecture that the present sequence can be constructed simply as a union of highly composite numbers and deeply composite numbers. The latter uses A095848's all-sufficiently-low-power definition with real exponents: one negative real threshold, and every real exponent below it. The threshold may depend on n. No lexicographic equivalence is assumed. The complete iff was preregistered in public issue 8081 on September 15, 2026, at 11:22:40 UTC, before numerical or Lean probes.

**Theorem 1.4 (Negation of the complete union claim).**

$$\neg (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow ((\exists x \in \mathbb{R},\; (x \le 0) \land (\operatorname{StrictDivisorPowerRecord}\left(n, x\right))) \Leftrightarrow ((\operatorname{StrictDivisorPowerRecord}\left(n, 0\right)) \lor (\exists B \in \mathbb{R},\; (B < 0) \land (\forall x \in \mathbb{R},\; (x \le B) \Rightarrow (\operatorname{StrictDivisorPowerRecord}\left(n, x\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396596-divisor-power-union` (refuted) by `D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396596-divisor-power-union","declaration_gid":"D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hal M. Switkay (2026). *OEIS A396596: divisor-power records and the highly/deeply composite union conjecture*. URL: <https://oeis.org/search?q=id:A396596&fmt=text>.

*Commentary.*

The result type is closed Not claim. The proof takes N = 32125373280 and exponent -4. Its record proof covers every positive predecessor: nonmultiples of L = 232792560 = lcm(1,...,19) and all smaller multiples.

A nonmultiple misses d and 2d for some 1 <= d <= 19. A local telescoping reciprocal-fourth-power estimate bounds every finite positive-divisor sum; inserting those two missing terms puts the nonmultiple below N. The multiples are kL for 1 <= k <= 137. The exact 137-row certificate checks prime bases, pairwise coprimality, factorization and the cross-multiplied sigma inequality. Local induction proves certificate soundness and reciprocal divisor pairing connects sigma_4(n)/n^4 to the original real divisor sum.

At zero, the smaller predecessor 27935107200 ties N's 3072 divisors, excluding a strict record. For every real x <= -1000, predecessor 26771144400 wins: N-only divisors are at least 27, whereas 25 divides the predecessor but not N, and N*27^x < 25^x. For arbitrary real B < 0, min(B,-1000) therefore defeats the eventual-record alternative.

Empirical candidate discovery is separate from the exact full-domain argument. No floating-point proof or prime-signature completeness assumption is used. There is no minimality claim or claim that all superabundant numbers fall outside either class.

Semantic assessment: proof_shape content; computational kind certified-instance, also bounded-enumeration; utility refutes the displayed claim; admission_basis open-problem-resolution; escape_witness none. The closed refutation preserves the exact original claim. No direct frozen project dependency or atom coverage is asserted. The source note and Problems dossier retain the bounded search and attribution limits.

## References

- Truth anchor: `D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.DivisorPowerSum`
- Truth anchor: `D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.StrictDivisorPowerRecord`
- Truth anchor: `D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.claim`
- Truth anchor: `D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation.result`
