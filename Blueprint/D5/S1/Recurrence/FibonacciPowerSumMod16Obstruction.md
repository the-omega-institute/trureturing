# Fibonacci Perfect-Power Sum Obstruction Modulo Sixteen

## Abstract

Fibonacci residues modulo sixteen give a finite obstruction to even perfect-power sums.

**Definition 1.1 (Square residues modulo sixteen).**

$$R_{16}: \operatorname{Finset}(\mathbb{N}) := \left\{0, 1, 4, 9\right\}.$$

*Formalization.* `D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.squareResidues16` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This finite set is the target of the exhaustive square-residue classification and the complement used in the obstruction set.

**Theorem 1.2 (Fibonacci period and index reduction modulo sixteen).**

$$\begin{aligned}\left(\forall n: \mathbb{N}, \operatorname{fib}(n + 24) \bmod 16 = \operatorname{fib}(n) \bmod 16\right) \land\\\left(\forall n: \mathbb{N}, \operatorname{fib}(n) \bmod 16 = \operatorname{fib}(n \bmod 24) \bmod 16\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.fib_mod_sixteen_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two kernel-computed initial congruences and the two-step Fibonacci recurrence establish period twenty-four. Induction on the quotient by twenty-four then reduces every index to its remainder.

**Theorem 1.3 (Classification of squares modulo sixteen).**

$$\forall y: \mathbb{N}, {y}^{2} \bmod 16 \in R_{16}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.square_mod_sixteen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reducing the base modulo sixteen leaves sixteen cases, each discharged by kernel evaluation.

**Definition 1.4 (Obstructed residue pairs).**

$$E_{16}: \operatorname{Finset}(\operatorname{Fin}(24) \times \operatorname{Fin}(24)) := \left\{(r, s) \mid (r, s) \in \operatorname{Fin}(24) \times \operatorname{Fin}(24), \neg {\left(\operatorname{fib}(r) + \operatorname{fib}(s)\right) \bmod 16 \in R_{16}}\right\}.$$

*Formalization.* `D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.E16` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set contains exactly those ordered residues modulo twenty-four whose Fibonacci sum is not a square residue modulo sixteen.

**Theorem 1.5 (Cardinality of the obstruction set).**

$$\operatorname{card}(E_{16}) = 440.$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.E16_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ordinary kernel decision, with only the recursion-depth option raised locally, counts 440 obstructed pairs among the 576 possibilities.

**Theorem 1.6 (Even perfect powers are excluded on every obstructed residue pair).**

$$\begin{gathered}\left(\forall n, m: \mathbb{N},\\(n \bmod 24, m \bmod 24) \in E_{16} \implies\\\forall y, a: \mathbb{N},\\\operatorname{Even}(a) \implies 2 \le a \implies\\{y}^{a} \neq \operatorname{fib}(n) + \operatorname{fib}(m)\right) \land\\\left(\operatorname{fib}(36) + \operatorname{fib}(12) = {3864}^{2}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.even_power_sum_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An even exponent writes the power as a square. Equality with a Fibonacci sum would therefore put its residue in the square set, while period reduction transfers that residue to the pair already excluded by E16.

The second conjunct is the source's independent numerical check: Fibonacci numbers at indices thirty-six and twelve sum to the square of 3864. This modular result does not prove the full Luca-Patel conjecture.

## References

- Truth anchor: `D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.E16`
- Truth anchor: `D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.E16_card`
- Truth anchor: `D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.even_power_sum_obstruction`
- Truth anchor: `D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.fib_mod_sixteen_period`
- Truth anchor: `D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.squareResidues16`
- Truth anchor: `D5/S1/Recurrence/FibonacciPowerSumMod16Obstruction.square_mod_sixteen`
