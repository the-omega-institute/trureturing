# Frid prefix lengths in Fibonacci numeration

## Abstract

Frid prefix lengths in Fibonacci numeration

**Definition 1.1 (N).**

$$\forall k \in \mathbb{N},\; N\left(k\right) = fst\left(fibPair\left(append\left(wordPower\left(2 \cdot k - 1, list\left(1, 0, 0\right)\right), list\left(1, 0, 1\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/FridNumerals.N` (`✓ std3`).

*Citation.* Anna E. Frid (2018). *Representations of palindromes in the Fibonacci word*. URL: <https://numeration2018.sciencesconf.org/data/pages/num18_abstracts.pdf>.

*Commentary.*

Conjecture 2 on printed page 12 states: “For every k ≥ 1, the prefix of the Fibonacci word of length (100)²ᵏ⁻¹101 cannot be decomposed as a concatenation of at most 2k palindromes.” N(k) is the value of its stated numeral. The digits are read most significant first. wordPower repeats the block [1,0,0]. fibPair uses weights G(0)=1 and G(1)=2. The natural subtraction 2k-1 is truncated at zero; the conjecture only uses k at least one.

**Theorem 1.2 (frid_numeral_twice).**

$$\forall m \in \mathbb{N},\; 2 \cdot fst\left(fibPair\left(append\left(wordPower\left(m, list\left(1, 0, 0\right)\right), list\left(1, 0, 1\right)\right)\right)\right) = fib\left(3 \cdot m + 6\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/FridPrefix/FridNumerals.frid_numeral_twice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Fibonacci recurrence yields this exact integer identity by induction on the repeated block. Here fib(0)=0 and fib(1)=1.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/FridNumerals.N`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/FridNumerals.frid_numeral_twice`
- Dependency: [D5/S1/Digit/GoldenBase4IntervalMachine](../../../Digit/GoldenBase4IntervalMachine.md)
