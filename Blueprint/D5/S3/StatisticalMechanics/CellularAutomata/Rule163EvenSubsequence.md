# Rule 163 and the even subsequence of A392003

## Abstract

The full integer-lattice evolution of Rule 163 from a single ON cell gives the even subsequence of OEIS A392003 and the closed form, two recurrences and generating function of A266753.

**Definition 1.1 (Wolfram rule 163).**

$$\forall l \in \operatorname{Bool},\; \forall c \in \operatorname{Bool},\; \forall r \in \operatorname{Bool},\; \operatorname{rule163}\left(l, c, r\right) = \operatorname{Nat}.\operatorname{testBit}\left(163, 4 \cdot \operatorname{Bool}.\operatorname{toNat}\left(l\right) + 2 \cdot \operatorname{Bool}.\operatorname{toNat}\left(c\right) + \operatorname{Bool}.\operatorname{toNat}\left(r\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.rule163` (`✓ std3`).

*Citation.* Karl-Heinz Hofmann; Robert Price; Colin Barker; Yosu Yurramendi (2025). *OEIS A392003 and A266753: the Rule 163 even-subsequence, closed-form, recurrence and generating-function conjectures*. URL: <https://oeis.org/A392003>.

*Commentary.*

The output is bit 4l + 2c + r of 163, with false and true read as 0 and 1. In neighborhood order 111,110,101,100,011,010,001,000, the outputs are 1,0,1,0,0,0,1,1. The exterior is updated at every time step; both 000 and 111 produce 1.

**Definition 1.2 (The cellular sequence A266753).**

$$\forall n \in \mathbb{N},\; \operatorname{A}\left(n\right) = \sum_{j \in \operatorname{Finset}.\operatorname{range}\left(2 \cdot n + 1\right)} \operatorname{Bool}.\operatorname{toNat}\left(\operatorname{D5}.\operatorname{S0}.\operatorname{Automata}.\operatorname{RuleThirtyTwentyTwoMersenneSignRefutation}.\operatorname{row}\left(\operatorname{rule163}, n, (n: \mathbb{Z}) - (j: \mathbb{Z})\right)\right) \cdot 2^{j}$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.A` (`✓ std3`).

*Citation.* Karl-Heinz Hofmann; Robert Price; Colin Barker; Yosu Yurramendi (2025). *OEIS A392003 and A266753: the Rule 163 even-subsequence, closed-form, recurrence and generating-function conjectures*. URL: <https://oeis.org/A392003>.

*Commentary.*

OEIS A266753, NAME (revision 49, unpaginated): Decimal representation of the n-th iteration of the "Rule 163" elementary cellular automaton starting with a single ON (black) cell. The source program reads cells -n through n from left to right in base 2. The coordinate n-j has weight 2^j; row 0 has only its origin ON, and row is the existing evolution on all integer cells.

**Definition 1.3 (The explicit sequence A392003).**

$$\forall m \in \mathbb{N},\; \operatorname{B}\left(m\right) = \frac{7 \cdot (2: \mathbb{Q})^{m} - 9 + 5 \cdot (-1: \mathbb{Q})^{m}}{6}$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.B` (`✓ std3`).

*Citation.* Karl-Heinz Hofmann; Robert Price; Colin Barker; Yosu Yurramendi (2025). *OEIS A392003 and A266753: the Rule 163 even-subsequence, closed-form, recurrence and generating-function conjectures*. URL: <https://oeis.org/A392003>.

*Commentary.*

OEIS A392003, NAME (revision 30, unpaginated): a(n) = (7*2^n - 9 + 5*(-1)^n) / 6. The source offset is 1: only positive indices are used in the subsequence equation. The division is in the rational numbers.

**Definition 1.4 (The five source assertions).**

$$claim \Leftrightarrow ((\forall n \in \mathbb{N},\; 1 \le n \Rightarrow (\operatorname{B}\left(2 \cdot n\right) = (\operatorname{A}\left(n\right): \mathbb{Q}))) \land ((\forall n \in \mathbb{N},\; 1 < n \Rightarrow ((\operatorname{A}\left(n\right): \mathbb{Q}) = \frac{7 \cdot (4: \mathbb{Q})^{n} - 4}{6})) \land ((\forall n \in \mathbb{N},\; 1 < n \Rightarrow (\operatorname{A}\left(n\right) = 4 \cdot \operatorname{A}\left(n - 1\right) + 2)) \land ((\forall n \in \mathbb{N},\; 2 < n \Rightarrow ((\operatorname{A}\left(n\right): \mathbb{Z}) = 5 \cdot (\operatorname{A}\left(n - 1\right): \mathbb{Z}) - 4 \cdot (\operatorname{A}\left(n - 2\right): \mathbb{Z}))) \land (\operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{fun} (n: \mathbb{N}) \mapsto (\operatorname{A}\left(n\right): \mathbb{Z})\right) \cdot ((1 - \operatorname{PowerSeries}.\operatorname{X}) \cdot (1 - 4 \cdot \operatorname{PowerSeries}.\operatorname{X})) = 1 - \operatorname{PowerSeries}.\operatorname{X} + 2 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2})))))$$

*Formalization.* `D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.claim` (`✓ std3`).

*Citation.* Karl-Heinz Hofmann; Robert Price; Colin Barker; Yosu Yurramendi (2025). *OEIS A392003 and A266753: the Rule 163 even-subsequence, closed-form, recurrence and generating-function conjectures*. URL: <https://oeis.org/A392003>.

*Commentary.*

OEIS A392003, FORMULA (revision 30, unpaginated): Conjecture: a(2*n) = A266753(n). OEIS A266753, FORMULA (revision 49, unpaginated): Conjectures from _Colin Barker_, Jan 20 2016 and Apr 20 2019: (Start) a(n) = 5*a(n-1)-4*a(n-2) for n>2. G.f.: (1-x+2*x^2) / ((1-x)*(1-4*x)). (End) Empirical a(n) = (7*4^n - 4)/6 for n>1. - _Colin Barker_, Nov 25 2016 and Apr 20 2019 a(n) = 4*a(n-1) + 2, n>1, conjectured. - _Yosu Yurramendi_, Jan 22 2017 Here A is the cellular sequence, B is the explicit rational sequence, and n is natural. The five clauses use n>=1, n>1, n>1, n>2, and all formal-series coefficients respectively. Subtractions in the indices are natural subtraction; the second-order equation and series have integer coefficients.

**Theorem 1.5 (Proof of the five assertions).**

$$(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow (\operatorname{B}\left(2 \cdot n\right) = (\operatorname{A}\left(n\right): \mathbb{Q}))) \land ((\forall n \in \mathbb{N},\; 1 < n \Rightarrow ((\operatorname{A}\left(n\right): \mathbb{Q}) = \frac{7 \cdot (4: \mathbb{Q})^{n} - 4}{6})) \land ((\forall n \in \mathbb{N},\; 1 < n \Rightarrow (\operatorname{A}\left(n\right) = 4 \cdot \operatorname{A}\left(n - 1\right) + 2)) \land ((\forall n \in \mathbb{N},\; 2 < n \Rightarrow ((\operatorname{A}\left(n\right): \mathbb{Z}) = 5 \cdot (\operatorname{A}\left(n - 1\right): \mathbb{Z}) - 4 \cdot (\operatorname{A}\left(n - 2\right): \mathbb{Z}))) \land (\operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{fun} (n: \mathbb{N}) \mapsto (\operatorname{A}\left(n\right): \mathbb{Z})\right) \cdot ((1 - \operatorname{PowerSeries}.\operatorname{X}) \cdot (1 - 4 \cdot \operatorname{PowerSeries}.\operatorname{X})) = 1 - \operatorname{PowerSeries}.\operatorname{X} + 2 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Karl-Heinz Hofmann; Robert Price; Colin Barker; Yosu Yurramendi (2025). *OEIS A392003 and A266753: the Rule 163 even-subsequence, closed-form, recurrence and generating-function conjectures*. URL: <https://oeis.org/A392003>.

*Commentary.*

For every positive time n, the entire row is 1 outside [-n,n], and the central word is 100 followed by n-1 copies of 10. Induction checks the three old neighbors at every integer coordinate, including the moving boundaries. Appending 10 multiplies the binary value by 4 and adds 2, so A(n+1)=4*A(n)+2 for n at least 1. Induction gives 6*A(n)+4=7*4^n; the rational closed form holds already at n=1. Substitution at even indices gives the subsequence identity, and eliminating the constant term from two successive first-order equations gives the second-order recurrence. Comparing coefficients of the formal power series uses A(0)=1, A(1)=4 and A(2)=18, then the second-order recurrence in every degree at least 3. The two denominator factors have constant term 1, so the product equation expresses the source rational generating function without analytic convergence assumptions.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.A`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.B`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.result`
- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.rule163`
- Dependency: [D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation](../../../S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.md)
