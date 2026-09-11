# The Least Simultaneous Digit-Sum Witness

## Abstract

Wu's conjecture for the least simultaneous digit-sum witness in OEIS A389000.

The sequence definition and the conjecture are those of OEIS A389000 (Chai Wah Wu, October 1, 2025), recorded in the literature note wu2025a389000. The OEIS rendering 210^(2*m+1)-1 means 2 times 10^(2*m+1), minus 1.

All variables and operations are over the natural numbers. The notation digits(10,x) means Nat.digits 10 x, and sum means List.sum. Subtraction is natural subtraction. The natural infimum selects the least member of a nonempty set and is zero for an empty set.

**Definition 1.1 (Base-ten digit sum).**

$$\forall x \in \mathbb{N}, \operatorname{digitSum}(x) = \operatorname{sum}(\operatorname{digits}(10,x))$$

*Formalization.* `D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.digitSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This definition binds Mathlib's base-ten digits and list sum.

**Definition 1.2 (The least positive witness).**

$$\forall n \in \mathbb{N}, \operatorname{a}(n) = \operatorname{sInf}(\{k \in \mathbb{N} \mid 0 < k \land (n \mid \operatorname{digitSum}(k) \land n \mid \operatorname{digitSum}(k^{2}))\})$$

*Formalization.* `D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining set requires positivity and both divisibility conditions. The two digit-sum identities below make it nonempty at every index 9m+5.

**Theorem 1.3 (The candidate's digit sum).**

$$\forall m \in \mathbb{N}, \operatorname{digitSum}(2 \cdot 10^{2 \cdot m + 1} - 1) = 2 \cdot (9 \cdot m + 5)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.digitSum_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the number of trailing nines gives digitSum(c times 10^d minus 1) equal to 9d+c-1 for 1 <= c <= 10. Taking c=2 and d=2m+1 gives the identity.

**Theorem 1.4 (The square's digit sum).**

$$\forall m \in \mathbb{N}, \operatorname{digitSum}((2 \cdot 10^{2 \cdot m + 1} - 1)^{2}) = 2 \cdot (9 \cdot m + 5)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.digitSum_witness_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With d=2m, the square is 10 times (10^d times (10 times (4 times 10^d minus 1) plus 6)) plus 1. Digit recursion removes the final 1 and the zero block, then the final 6. The remaining digit sum is 9d+3, giving 9d+10 overall.

**Theorem 1.5 (Wu's conjecture).**

$$\forall m \in \mathbb{N}, \operatorname{a}(9 \cdot m + 5) = 2 \cdot 10^{2 \cdot m + 1} - 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.wu_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a389000-digit-sum-square-least-witness` (proved) by `D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.wu_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a389000-digit-sum-square-least-witness","declaration_gid":"D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.wu_conjecture","resolution_kind":"proved"} -->

*Citation.* Chai Wah Wu (2025). *OEIS A389000, least k with n dividing the digit sums of k and k^2*. URL: <https://oeis.org/A389000>.

*Commentary.*

Put n=9m+5, L=2m+1, and K=2 times 10^L minus 1. An inductive leading-digit ceiling and its equality case show that 0<k<K implies digitSum(k)<2n. If n divides this positive sum, it equals n. Mathlib's mod-nine digit-sum congruence then gives k mod 9 = 5 and digitSum(k^2) mod 9 = 7. Writing digitSum(k^2)=nt yields 5t mod 9 = 7, so t>=5. But k^2<4 times 10^(2L) gives digitSum(k^2)<=18L+3=36m+21<5n, a contradiction. The candidate satisfies both divisibility conditions, hence is the least element.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.a`
- Truth anchor: `D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.digitSum`
- Truth anchor: `D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.digitSum_witness`
- Truth anchor: `D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.digitSum_witness_sq`
- Truth anchor: `D5/S1/Digit/Admissibility/DigitSumSquareLeastWitness.wu_conjecture`
