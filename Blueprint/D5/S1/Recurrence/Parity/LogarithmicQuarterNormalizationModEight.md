# Logarithmic Quarter Normalization Modulo Eight

## Abstract

The positive-index coefficients of OEIS A396846 repeat 1, 7, 5, 7 modulo eight.

The second conjecture in hanna2026a396846 concerns the logarithmic generating function with argument 1+x+Sum 4n a(n)x^n/(4n^2-1). Its formal meaning is B H = X H', with constant coefficient of H equal to one. The series with positive-degree coefficients a(n)/n and zero constant coefficient is therefore the formal logarithm of H.

Indices are natural numbers, and subtraction in an index is natural subtraction. The sequences a and c take integer values; their values and natural indices are embedded in the rational numbers in rational formulas. The expression 4n^2-1 uses ring subtraction. The notation mod is integer remainder, range(n) is 0<=k<n, and Ico(r,n) is r<=k<n. The operator mk constructs a formal series from its coefficient function; mapInt applies the canonical integer-to-rational ring homomorphism. The symbol X is the formal indeterminate in the indicated coefficient ring.

**Definition 1.1 (Integral normalized coefficients).**

$$\begin{aligned}\operatorname{c}: \mathbb{N} \to \mathbb{Z}\\\forall n: \mathbb{N}, \operatorname{c}\left(n\right) = (\operatorname{if} (2 \le n) \operatorname{then} (\operatorname{if} (n - 1 = 1) \operatorname{then} 1 \operatorname{else} (4 \cdot (n - 1)^{2} - 1) \cdot \operatorname{c}\left(n - 1\right)) + 4 \cdot \sum_{k \in \operatorname{range}\left(n\right)} ((\operatorname{if} ((2 \le k) \land (k < n)) \operatorname{then} k \cdot \operatorname{c}\left(k\right) \cdot (\operatorname{if} (n - k = 1) \operatorname{then} 1 \operatorname{else} (4 \cdot (n - k)^{2} - 1) \cdot \operatorname{c}\left(n - k\right)) \operatorname{else} 0)) \operatorname{else} 0)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The guarded recursion uses only smaller indices and sets c(0)=c(1)=0.

**Definition 1.2 (The coefficient sequence).**

$$\begin{aligned}\operatorname{a}: \mathbb{N} \to \mathbb{Z}\\\forall n: \mathbb{N}, \operatorname{a}\left(n\right) = (\operatorname{if} (n = 1) \operatorname{then} 1 \operatorname{else} (4 \cdot (n)^{2} - 1) \cdot \operatorname{c}\left(n\right))\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient at one is one. All other coefficients are obtained by multiplying c(n) by 4n^2-1; in particular a(0)=0.

**Theorem 1.3 (The integral convolution recurrence).**

$$\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{c}\left(n\right) = \operatorname{a}\left(n - 1\right) + 4 \cdot \sum_{k \in \operatorname{Ico}\left(2, n\right)} (k \cdot \operatorname{c}\left(k\right) \cdot \operatorname{a}\left(n - k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.c_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing the guards from the well-founded definition restricts the sum to 2<=k<n. The coefficient of c(n) is one.

**Theorem 1.4 (The integral normalization).**

$$\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{a}\left(n\right) = (4 \cdot (n)^{2} - 1) \cdot \operatorname{c}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.a_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>=2 the integer a(n) is (4n^2-1)c(n).

**Definition 1.5 (The logarithm argument).**

$$H: \operatorname{PowerSeries}\left(\mathbb{Z}\right), H = \operatorname{mk}\left((n \mapsto (\operatorname{if} (n = 0) \operatorname{then} 1 \operatorname{else} (\operatorname{if} (n = 1) \operatorname{then} 1 \operatorname{else} 4 \cdot n \cdot \operatorname{c}\left(n\right))))\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant and linear coefficients are one, and coefficient n>=2 is 4n c(n).

**Definition 1.6 (The ordinary coefficient series).**

$$B: \operatorname{PowerSeries}\left(\mathbb{Z}\right), B = \operatorname{mk}\left(\operatorname{a}\right)$$

*Formalization.* `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series B has coefficient a(n) at every natural index.

**Theorem 1.7 (The formal logarithmic equation).**

$$B \cdot H = X \cdot \operatorname{derivative}\left(\mathbb{Z}, H\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.log_derivative_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient comparison separates the constant and linear factors in the product B H. The remaining convolution is the defining recurrence for c; together with a(n)=(4n^2-1)c(n), it equals n times coefficient n of H.

**Theorem 1.8 (The exact rational coefficient shape).**

$$\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{coeff}\left(n, \operatorname{mapInt}\left(H\right)\right) = \frac{4 \cdot n}{4 \cdot (n)^{2} - 1} \cdot \operatorname{a}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.coeff_H_rat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>=2 the denominator 4n^2-1 is nonzero. Substituting the integral normalization gives exactly the logarithm argument in hanna2026a396846.

**Theorem 1.9 (Uniqueness among rational solutions).**

$$\forall b: \mathbb{N} \to \mathbb{Q}, \forall h: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (b\left(0\right) = 0) \implies ((b\left(1\right) = 1) \implies ((\operatorname{coeff}\left(0, h\right) = 1) \implies ((\operatorname{coeff}\left(1, h\right) = 1) \implies ((\forall n: \mathbb{N}, (2 \le n) \implies (\operatorname{coeff}\left(n, h\right) = \frac{4 \cdot n}{4 \cdot (n)^{2} - 1} \cdot b\left(n\right))) \implies ((\operatorname{mk}\left(b\right) \cdot h = X \cdot \operatorname{derivative}\left(\mathbb{Q}, h\right)) \implies (\forall n: \mathbb{N}, b\left(n\right) = \operatorname{a}\left(n\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.generating_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction compares coefficient n of the logarithmic equations. All interior convolution terms agree by the induction hypothesis. Clearing the nonzero denominator leaves equality of the nth coefficients.

**Theorem 1.10 (Every positive-index coefficient is odd).**

$$\forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.all_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recurrence makes c(n) congruent to a(n-1) modulo two, and its normalizing factor 4n^2-1 is odd. Induction starts at a(1)=1.

**Theorem 1.11 (The second A396846 conjecture).**

$$\forall n: \mathbb{N}, (1 \le n) \implies ((((n \bmod 4 = 1) \implies (\operatorname{a}\left(n\right) \bmod 8 = 1)) \land (((n \bmod 4 = 2) \implies (\operatorname{a}\left(n\right) \bmod 8 = 7)) \land (((n \bmod 4 = 3) \implies (\operatorname{a}\left(n\right) \bmod 8 = 5)) \land ((n \bmod 4 = 0) \implies (\operatorname{a}\left(n\right) \bmod 8 = 7))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.hanna_conjecture` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a396846-logarithmic-quarter-normalization-mod-eight` (proved) by `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.hanna_conjecture`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a396846-logarithmic-quarter-normalization-mod-eight","declaration_gid":"D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.hanna_conjecture","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A396846, l.g.f. log(1 + x + Sum 4n/(4n^2-1) a(n) x^n), mod-8 conjecture*. URL: <https://oeis.org/A396846>.

*Commentary.*

Oddness makes each normalized convolution term congruent to its index modulo two. Multiplication by four reduces the convolution modulo eight to four times the sum of indices 2<=k<n. This is four for n congruent to zero or one modulo four and zero otherwise. Induction through the four index classes yields the asserted repeating residues.

## References

- Truth anchor: `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.B`
- Truth anchor: `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.H`
- Truth anchor: `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.a`
- Truth anchor: `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.a_eq`
- Truth anchor: `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.all_odd`
- Truth anchor: `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.c`
- Truth anchor: `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.c_recurrence`
- Truth anchor: `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.coeff_H_rat`
- Truth anchor: `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.generating_unique`
- Truth anchor: `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.hanna_conjecture`
- Truth anchor: `D5/S1/Recurrence/Parity/LogarithmicQuarterNormalizationModEight.log_derivative_identity`
