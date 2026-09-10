# Parity of the Piecewise Convolution Sequence A368628

## Abstract

The piecewise square and fourth-power convolution has odd coefficients exactly at base-four repunits.

All indices and sequence values are natural numbers. Write A for series, the ordinary generating series with coefficients seq. The source equation is A(x)=1+x(A(x)^2-A(-x)^2)/2+x(A(x)^4+A(-x)^4)/2. Taking coefficients gives a square convolution at positive even indices and a fourth-power convolution at odd indices. The source entry states the parity description below as a conjecture; the argument here proves it from that recurrence.

The notation coeff(d,f) extracts degree d, mk forms a power series from a coefficient function, and ite selects its second argument when the first holds and its third otherwise. Subtraction in indices is natural subtraction. The notation cast(v,ZMod(2)) means reduction modulo two.

**Definition 1.1 (The original convolution definition).**

$$\forall n: \mathbb{N}, \operatorname{seq}\left(n\right) = \operatorname{ite}\left(n = 0, 1, \operatorname{coeff}\left(n - 1, \operatorname{mk}\left((i: \mathbb{N} \mapsto \operatorname{ite}\left(i < n, \operatorname{seq}\left(i\right), 0\right))\right)^{\operatorname{ite}\left(\operatorname{Even}\left(n\right), 2, 4\right)}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.seq` (`✓ std3`).

*Citation.* Paul D. Hanna; OEIS Foundation Inc. (2024). *A368628 — a piecewise square and fourth-power generating function*. URL: <https://oeis.org/A368628>.

*Commentary.*

Well-founded recursion defines seq(n) using only values at indices below n. The auxiliary coefficient function is zero outside that interval. Since the requested coefficient has degree n-1, every factor in its finite convolution has index below n; the zero extension cannot change the result. The parity pattern is not part of this definition.

**Definition 1.2 (The natural-number generating series).**

$$A = \operatorname{mk}\left(seq\right)$$

*Formalization.* `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.series` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A is a power series over the natural numbers, with coefficient n equal to seq(n).

**Theorem 1.3 (Initial value).**

$$\operatorname{seq}\left(0\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.seq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial clause of the defining recurrence gives the constant coefficient one.

**Theorem 1.4 (The exact coefficient recurrence).**

$$\forall n: \mathbb{N}, (0 < n) \implies \operatorname{seq}\left(n\right) = \operatorname{coeff}\left(n - 1, A^{\operatorname{ite}\left(\operatorname{Even}\left(n\right), 2, 4\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.seq_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the exponent of a power shows that equal coefficients through degree n-1 give equal coefficients of that power through the same degree. Apply this to remove the zero extension in the defining recurrence.

**Theorem 1.5 (Positive even indices vanish modulo two).**

$$\forall j: \mathbb{N}, \operatorname{cast}\left(\operatorname{seq}\left(2 \cdot j + 2\right), \operatorname{ZMod}\left(2\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.seq_even_index_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the existing convolution_pairing theorem to the series g=X A(X squared). Its constant coefficient and every even coefficient vanish. The coefficient of g squared at degree 4(j+1) is therefore zero, while expansion and the factor X squared identify it with degree 2j+1 of A squared. The even-index recurrence transfers this cancellation to seq(2j+2).

**Theorem 1.6 (Indices congruent to three modulo four vanish).**

$$\forall j: \mathbb{N}, \operatorname{cast}\left(\operatorname{seq}\left(4 \cdot j + 3\right), \operatorname{ZMod}\left(2\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.seq_four_mul_add_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Frobenius over ZMod(2), applied twice, identifies the fourth power with expansion by four. Its coefficients at degrees 4j+2 vanish. The odd-index recurrence then gives the displayed sequence value.

**Theorem 1.7 (Parity descends through indices congruent to one).**

$$\forall j: \mathbb{N}, \operatorname{cast}\left(\operatorname{seq}\left(4 \cdot j + 1\right), \operatorname{ZMod}\left(2\right)\right) = \operatorname{cast}\left(\operatorname{seq}\left(j\right), \operatorname{ZMod}\left(2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.seq_four_mul_add_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same fourth-power identity says its coefficient at degree 4j equals the original coefficient at degree j. Reducing the odd-index recurrence modulo two yields the equality.

**Theorem 1.8 (The parity conjecture for all indices).**

$$\forall n: \mathbb{N}, \operatorname{Odd}\left(\operatorname{seq}\left(n\right)\right) \Leftrightarrow (\exists k: \mathbb{N}, 3 \cdot n + 1 = 4^{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.a368628_odd_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction starts at n=0. Positive even indices and indices 4j+3 are excluded both by the coefficient reductions and by the residues of 4 to a natural power. At n=4j+1, parity descends to j<n, and 3n+1=4(3j+1) advances the exponent by one. Conversely, a positive exponent can be decreased by one, so the same induction proves both directions.

## References

- Truth anchor: `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.a368628_odd_iff`
- Truth anchor: `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.seq`
- Truth anchor: `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.seq_even_index_zero`
- Truth anchor: `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.seq_four_mul_add_one`
- Truth anchor: `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.seq_four_mul_add_three`
- Truth anchor: `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.seq_recurrence`
- Truth anchor: `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.seq_zero`
- Truth anchor: `D5/S1/Recurrence/PiecewiseConvolutionPowersOfFour.series`
- Dependency: [D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo](ConvolutionRecurrenceOddPowersOfTwo.md)
