# Actual ordinary-avoider peak polynomials

## Abstract

Actual ordinary ascent words with literal adjacent-pair avoidance and exact boundary conditions.

**Definition 1.1 (wordPeakPolynomial).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.wordPeakPolynomial`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.wordPeakPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The finite sum of y raised to n minus strict ascents over the actual length-n ordinary words avoiding literal 10-1 and 20-1.

**Definition 1.2 (dyckPeakPolynomial).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.dyckPeakPolynomial`

*Formalization.* `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.dyckPeakPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The finite sum of y raised to the adjacent UD peak count over actual Mathlib Dyck words of semilength n.

**Theorem 1.3 (wordPeakPolynomial_eq).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.wordPeakPolynomial_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.wordPeakPolynomial_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The proved actual equivalence transports the entire finite weighted sum from ordinary avoiders to the Dyck peak polynomial.

**Theorem 1.4 (coeff_dyckPeakPolynomial).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.coeff_dyckPeakPolynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.coeff_dyckPeakPolynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Every coefficient of the Dyck peak polynomial is the cardinality of the corresponding actual peak fiber.

**Theorem 1.5 (coeff_wordPeakPolynomial).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.coeff_wordPeakPolynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.coeff_wordPeakPolynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The actual ordinary-word weighted polynomial has Narayana coefficients whenever (n,k) is not (1,0). This explicitly retains the licensed supplier boundary.

**Theorem 1.6 (coeff_one_zero).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.coeff_one_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.coeff_one_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

The actual semilength-one zero-peak coefficient is zero, separately handling the natural quotient exception.

**Theorem 1.7 (eval_one).**

Lean statement: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.eval_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.eval_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma and Wenlin Zhang (2026). *Ten Wilf classes, two pair equivalences and a Catalan bijection for ascent sequences (revision 3)*. URL: <https://github.com/the-omega-institute/trureturing/issues/29483#issuecomment-6832487181>.

*Commentary.*

Evaluation of the actual ordinary-word weighted polynomial at one recovers the Catalan total at every n, including zero. The formal-series functional equation and Lagrange inversion over Q[y] remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.coeff_dyckPeakPolynomial`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.coeff_one_zero`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.coeff_wordPeakPolynomial`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.dyckPeakPolynomial`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.eval_one`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.wordPeakPolynomial`
- Truth anchor: `D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanPolynomial.wordPeakPolynomial_eq`
- Dependency: [D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentCatalanStatistics](OrdinaryAscentCatalanStatistics.md)
