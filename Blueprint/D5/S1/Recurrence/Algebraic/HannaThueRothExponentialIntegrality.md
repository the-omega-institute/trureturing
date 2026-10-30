# Hanna's Thue/Roth Exponential Integrality

## Abstract

Hanna's Thue/Roth weighted formal exponential has integer coefficients.

**Definition 1.1 (The Thue/Roth bits).**

$$\forall n: \mathbb{N}, \operatorname{b}\left(n\right) = if (n = 0) then 0 else (if (\operatorname{Nat.mod}\left(\operatorname{padicValNat}\left(3, n\right), 2\right) = 0) then 1 else 0)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality.b` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A174470: Thue/Roth weighted exponential integrality*. URL: <https://oeis.org/A174470>.

*Commentary.*

OEIS A014578, NAME field (no page number): “Binary expansion of Thue constant (or Roth's constant).” Its FORMULA field states: “a(0)=0; a(3k)=1-a(k) for k>=1; a(3k+1)=a(3k+2)=1 for k>=0. - _Benoit Cloitre_, Mar 19 2004”. Here b takes values in the integers. The zero term is zero; at a positive n, the value is one exactly when the three-adic valuation is even. Nat.mod is natural-number remainder.

**Definition 1.2 (The logarithmic weights).**

$$\forall n: \mathbb{N}, \operatorname{c}\left(n\right) = \operatorname{b}\left(n\right) \cdot (3: \mathbb{Z})^{n}$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality.c` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A174470: Thue/Roth weighted exponential integrality*. URL: <https://oeis.org/A174470>.

*Commentary.*

OEIS A174470, NAME field (no page number): “G.F.: exp( Sum_{n>=1} A014578(n)*(3x)^n/n ), where A014578 is the binary expansion of Thue constant.” The weight c(n) is b(n) times 3 to the n-th power.

**Definition 1.3 (The specified rational series).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(A\right) \iff (A = \operatorname{PowerSeries.subst}\left(\operatorname{DoldExponentialIntegrality.logInput}\left(c\right), \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality.IsSourceSeries` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A174470: Thue/Roth weighted exponential integrality*. URL: <https://oeis.org/A174470>.

*Commentary.*

OEIS A174470, NAME field (no page number): “G.F.: exp( Sum_{n>=1} A014578(n)*(3x)^n/n ), where A014578 is the binary expansion of Thue constant.” A is a rational formal power series. DoldExponentialIntegrality.logInput c has degree-n coefficient c(n)/n over the rationals and constant coefficient zero. PowerSeries.subst takes this input first and PowerSeries.exp ℚ second; no analytic convergence is required.

**Definition 1.4 (Hanna's integrality assertion).**

$$claim \iff ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSourceSeries}\left(A\right)) \implies (\forall N: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(N, A\right) = (z: \mathbb{Q}))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2010). *OEIS A174470: Thue/Roth weighted exponential integrality*. URL: <https://oeis.org/A174470>.

*Commentary.*

OEIS A174470, COMMENT field (no page number): “Conjectured to consist entirely of integers.” The NAME field reads: “G.F.: exp( Sum_{n>=1} A014578(n)*(3x)^n/n ), where A014578 is the binary expansion of Thue constant.” Existence of A is included. Every ordinary coefficient, at every natural degree N including zero, is the rational image of an integer z.

**Theorem 1.5 (All coefficients are integers).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSourceSeries}\left(A\right)) \implies (\forall N: \mathbb{N}, \exists z: \mathbb{Z}, \operatorname{PowerSeries.coeff}\left(N, A\right) = (z: \mathbb{Q})))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a174470` (proved) by `D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a174470","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2010). *OEIS A174470: Thue/Roth weighted exponential integrality*. URL: <https://oeis.org/A174470>.

*Commentary.*

The specified rational series exists and all its coefficients are integers. For the prime 3, the inequality v₃(m)+1 ≤ m makes both weights divisible by the required power of 3. At every other prime p, b(pm)=b(m), and Euler's congruence modulo p raised to vₚ(m)+1 supplies the power difference, including p=2. The Dold exponential-integrality theorem gives the conclusion at every natural degree, including the constant term.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality.IsSourceSeries`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality.b`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality.c`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaThueRothExponentialIntegrality.result`
- Dependency: [D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality](DoldExponentialIntegrality.md)
