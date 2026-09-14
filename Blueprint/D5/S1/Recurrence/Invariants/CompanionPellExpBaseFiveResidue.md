# Hanna's Companion Pell Exponential Residues

## Abstract

Hanna's A204061 residues mod 5 are one exactly when no base-5 digit is two.

The symbols N and Z denote the natural numbers and integers; Q_5 (ℚ₅) is the field of 5-adic numbers and Z_5 (ℤ₅) its ring of integers, with the primality fact Nat.prime_five supplied inline. PowerSeries(Q_5) is the formal power-series ring with indeterminate X. The operator exp(Q_5) denotes its formal exponential series, subst(F,E) substitutes E into F, and coeff(n,F) extracts coefficient n. The operator toZMod maps Z_5 to ZMod(5), the integers modulo five; digits_5(n) is the list of base-five digits of n, with digits_5(0) empty. The indices n and k are natural numbers. The exponent uses the frozen companion-Pell sequence Q of D5/S1/Recurrence/PellCompanionGcd (A001333, one-half the companion Pell numbers), and a is the exponential coefficient function. A type annotation in Q_5 indicates the canonical embedding of an integer, natural number, or 5-adic integer. The sum is formal, has zero constant coefficient, and uses division in Q_5.

**Definition 1.1 (The Pell-square exponential coefficients).**

$$\forall n: \mathbb{N}, (\operatorname{a}\left(n\right): \mathbb{Q}_{5}) = \operatorname{coeff}\left(n, \operatorname{subst}\left(\operatorname{exp}\left(\mathbb{Q}_{5}\right), (\sum_{k: \mathbb{N}, 1 \le k} (\frac{(\operatorname{Q}\left(k\right): \mathbb{Q}_{5})^{2} \cdot X^{k}}{(k: \mathbb{Q}_{5})}): \operatorname{PowerSeries}\left(\mathbb{Q}_{5}\right))\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CompanionPellExpBaseFiveResidue.a` (`✓ std3`).

*Citation.* Paul D. Hanna (2012). *OEIS A204061, G.f.: exp( Sum_{n>=1} A001333(n)^2 * x^n/n )*. URL: <https://oeis.org/A204061>.

*Commentary.*

The defining exponential of OEIS A204061 is read in Q_5. Its exponent uses the frozen companion-Pell sequence Q of D5/S1/Recurrence/PellCompanionGcd (A001333, one-half the companion Pell numbers). The coefficient formula directly uses that exponential, with a zero constant term in its exponent. Integrality over Z is not asserted.

**Theorem 1.2 (The A204061 base-five residue conjecture).**

$$\forall n: \mathbb{N}, \exists z: \mathbb{Z}_{5}, ((z: \mathbb{Q}_{5}) = \operatorname{a}\left(n\right)) \land (\operatorname{toZMod}\left(z\right) = (\operatorname{if} (2 \in \left(\operatorname{digits}_{5}\right)\left(n\right)) \operatorname{then} 0 \operatorname{else} 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CompanionPellExpBaseFiveResidue.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a204061-companion-pell-exp-base-five-residue` (proved) by `D5/S1/Recurrence/Invariants/CompanionPellExpBaseFiveResidue.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a204061-companion-pell-exp-base-five-residue","declaration_gid":"D5/S1/Recurrence/Invariants/CompanionPellExpBaseFiveResidue.result","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2012). *OEIS A204061, G.f.: exp( Sum_{n>=1} A001333(n)^2 * x^n/n )*. URL: <https://oeis.org/A204061>.

*Commentary.*

The squared Pell recurrence and formal differentiation give f(0)=1 and f^4(1+X)^2(1-6X+X^2)=1 for the exponential series f. A binomial series over Z_5 constructs an integral fourth root, which agrees with f by uniqueness at constant coefficient one. After reduction modulo five, Frobenius yields B=(1+X+X^3+X^4)B(X^5). Coefficient extraction and induction on n through n/5 give zero exactly when a digit two occurs, and one otherwise. The displayed residue law is Hanna's conjecture in this 5-adic reading.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CompanionPellExpBaseFiveResidue.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/CompanionPellExpBaseFiveResidue.result`
- Dependency: [D5/S1/Recurrence/PellCompanionGcd](../PellCompanionGcd.md)
