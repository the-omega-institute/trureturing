# The complete Barker series for actual minimal dominating subsets

## Abstract

The complete Barker series for actual minimal dominating subsets

**Definition 1.1 (lift).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.lift`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.lift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

A quotient integer vector is lifted to every full state by its literal class.

**Theorem 1.2 (intertwines).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.intertwines`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.intertwines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

For every quotient vector v, fullStep(lift v)=lift(step v). The proof applies the complete full-state successor permutation certificate and preserves every integer row multiplicity.

**Theorem 1.3 (lift orbit).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.lift_orbit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.lift_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

For every natural k, fullOrbit k equals lift(orbit k). The initial terminal certificate and the linear intertwining supply induction on every k.

**Theorem 1.4 (initial sum).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.initial_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.initial_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

For every quotient vector v, summing v at the classes of all 64 actual starts equals the sum of alpha(i)*v(i) over all 59 quotient classes.

**Definition 1.5 (numerator).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.numerator`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.numerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

The complete 49 integer coefficients of the source numerator include coefficient zero 0, coefficient one 2 and coefficient 48 −1. They reproduce Colin Barker, OEIS A286848, https://oeis.org/A286848, under CC-BY-SA-4.0, https://creativecommons.org/licenses/by-sa/4.0/.

**Definition 1.6 (evaluate).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.evaluate`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.evaluate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

The integer linear functional evaluates a quotient vector against all 59 entries of the exact initial row alpha.

**Definition 1.7 (quotientCoefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.quotientCoefficient`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.quotientCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

The scalar coefficient is 0 at index zero, 2 at index one, and evaluation of orbit(n−2) thereafter. This is defined separately from the actual subset count.

**Definition 1.8 (initialCoefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.initialCoefficient`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.initialCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

The initial range uses the exact certificate vectors values rather than assuming that they are powers.

**Theorem 1.9 (initial convolutions).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.initial_convolutions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.initial_convolutions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

Every convolution of the denominator with the initial coefficients in degrees zero through 49 equals the full literal numerator, with degree 49 zero.

**Theorem 1.10 (all later convolutions).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.all_later_convolutions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.all_later_convolutions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

For every m at least 50, the denominator convolution of quotientCoefficient at degree m is zero. Applying evaluate to shifted_annihilator(m−50) proves the entire unbounded range.

**Definition 1.11 (quotientSeries).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.quotientSeries`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.quotientSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

The rational formal power series has quotientCoefficient n cast to the rationals at each index n.

**Definition 1.12 (P).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.P`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

The numerator formal polynomial series uses all literal numerator coefficients in degrees zero through 48 and is zero thereafter.

**Definition 1.13 (Q).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.Q`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

The complete denominator is the finite sum of denominator(j) times X^j for every j in Fin 49. No leading or trailing coefficient is omitted.

**Theorem 1.14 (quotientSeries mul Q).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.quotientSeries_mul_Q`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.quotientSeries_mul_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

The product quotientSeries*Q equals P in rational formal power series. The proof separates the checked initial range zero through 49 from every later degree.

**Theorem 1.15 (Q constant).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.Q_constant`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.Q_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

The literal denominator has constant coefficient one.

**Theorem 1.16 (quotientSeries identity).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.quotientSeries_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.quotientSeries_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

The quotient-orbit series equals P*Q inverse. This theorem alone does not identify the quotient coefficients with actual subset counts.

**Theorem 1.17 (Every actual positive-width count).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.actualCount_quotient`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.actualCount_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

For every natural k, the actual labelled inclusion-minimal dominating subset count of the open grid of width k+2, cast to the integers, equals evaluate(orbit k). The proof uses the all-length actual word count and the total partition certificates, with no assumed recurrence or count relation.

**Definition 1.18 (The actual-subset series).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.actualSeries`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.actualSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

The rational formal power series has coefficient zero 0 and coefficient actualCount n at every positive n. The actual empty-grid count is not changed.

**Theorem 1.19 (The entire Colin Barker identity).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.whole_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.whole_identity` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a286848-barker-minimal-dominating-three-row-grids` (proved) by `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.whole_identity`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a286848-barker-minimal-dominating-three-row-grids","declaration_gid":"D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.whole_identity","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Colin Barker; Andrew Howroyd; OEIS Foundation Inc. (2017). *Number of minimal dominating sets in the grid graph P_3 X P_n*. URL: <https://oeis.org/A286848>.

*Commentary.*

actualSeries equals P times the inverse of Q in rational formal power series. P and Q contain every literal coefficient of Colin Barker's complete OEIS A286848 expression, including the leading x, both degree-48 terms, and denominator constant 1. All actual labelled inclusion-minimal dominating subsets are counted once for every width n at least 1.

The initial finite range and the shifted annihilator cover disjoint, exhaustive coefficient ranges. The denominator has constant term one, so its formal inverse exists over the rationals. Together with the actual-subset counting correspondence, this identifies every coefficient of the complete expression.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.P`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.Q`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.Q_constant`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.actualCount_quotient`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.actualSeries`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.all_later_convolutions`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.evaluate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.initialCoefficient`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.initial_convolutions`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.initial_sum`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.intertwines`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.lift`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.lift_orbit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.numerator`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.quotientCoefficient`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.quotientSeries`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.quotientSeries_identity`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.quotientSeries_mul_Q`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridSeries.whole_identity`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPartition](BarkerMinimalGridPartition.md)
- Dependency: [D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridPaths](BarkerMinimalGridPaths.md)
