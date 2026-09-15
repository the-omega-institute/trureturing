# Stephan's A181666 Odd-Part Characterization

## Abstract

Stephan's odd-part power characterization is equivalent to the A023758 difference form.

All variables are natural numbers, including zero. The named operator ordCompl[2] is Mathlib's 2-adic odd complement: it removes the full power of two from its argument, so ordCompl[2] n is the odd part of n. The displayed equations use natural-number addition, multiplication and powers only; no natural-number quotient is hidden in either predicate.

**Definition 1.1 (Membership in A181666).**

$$\forall n \in \mathbb{N},\; \operatorname{InA181666}\left(n\right) = \exists k \in \mathbb{N},\; (1 \le k) \land (3 \cdot \left(\operatorname{ordCompl}_{2}\right)\left(n\right) + 1 = 4^{k})$$

*Formalization.* `D5/S3/Arith/StephanOddPartPowerDifference.InA181666` (`✓ std3`).

*Citation.* Ralf Stephan (2010). *OEIS A181666, Numbers whose odd part is of the form (4^k-1)/3*. URL: <https://oeis.org/A181666>.

*Commentary.*

The predicate records exactly the OEIS name for A181666: the odd part of n has the form (4^k - 1)/3 for a positive exponent. It is written as 3 times the odd part plus one equals 4^k, which is an equivalent division-free expression over the natural numbers.

**Definition 1.2 (The A023758 quotient predicate).**

$$\forall n \in \mathbb{N},\; \operatorname{IsA023758DivThree}\left(n\right) = \exists i \in \mathbb{N}, j \in \mathbb{N},\; (j < i) \land (3 \cdot n + 2^{j} = 2^{i})$$

*Formalization.* `D5/S3/Arith/StephanOddPartPowerDifference.IsA023758DivThree` (`✓ std3`).

*Citation.* Ralf Stephan (2010). *OEIS A181666, Numbers whose odd part is of the form (4^k-1)/3*. URL: <https://oeis.org/A181666>.

*Commentary.*

The predicate describes a positive difference of powers of two divided by three without using natural subtraction: j is strictly below i and 3n plus 2^j equals 2^i. The strict inequality excludes the zero difference that would arise from i = j.

**Theorem 1.3 (The two descriptions are equivalent).**

$$\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow ((\exists k \in \mathbb{N},\; (1 \le k) \land (3 \cdot \left(\operatorname{ordCompl}_{2}\right)\left(n\right) + 1 = 4^{k})) \Leftrightarrow (\exists i \in \mathbb{N}, j \in \mathbb{N},\; (j < i) \land (3 \cdot n + 2^{j} = 2^{i})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/StephanOddPartPowerDifference.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a181666-stephan-odd-part-power-difference` (proved) by `D5/S3/Arith/StephanOddPartPowerDifference.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a181666-stephan-odd-part-power-difference","declaration_gid":"D5/S3/Arith/StephanOddPartPowerDifference.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ralf Stephan (2010). *OEIS A181666, Numbers whose odd part is of the form (4^k-1)/3*. URL: <https://oeis.org/A181666>.

*Commentary.*

For every n at least one, the two predicates are equivalent. From an odd-part witness k, the 2-adic exponent j of n and the exponent j + 2k give the required difference of powers. Conversely, a pair i > j with 3n + 2^j = 2^i has an even gap by reducing the equality modulo three; divisibility by three then isolates an odd quotient. The odd-complement decomposition recovers that quotient and the same exponent k. The positive-index hypothesis aligns the theorem with the source sequences, while the proof itself also makes both predicates false at n = 0.

## References

- Truth anchor: `D5/S3/Arith/StephanOddPartPowerDifference.InA181666`
- Truth anchor: `D5/S3/Arith/StephanOddPartPowerDifference.IsA023758DivThree`
- Truth anchor: `D5/S3/Arith/StephanOddPartPowerDifference.result`
