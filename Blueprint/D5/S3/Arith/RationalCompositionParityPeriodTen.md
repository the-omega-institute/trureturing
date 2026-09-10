# A396093 Parity Period Ten

## Abstract

Formula (2) for OEIS A396093 determines an integer sequence whose parity has period ten.

**Definition 1.1 (Factored numerator of formula (2)).**

$$N: \mathbb{Q}[[x]], (N = x \cdot (1 - x)^{2} \cdot (1 - 3 \cdot x + x^{2})^{2}).$$

*Formalization.* `D5/S3/Arith/RationalCompositionParityPeriodTen.N` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Proof: (definition). N is formula (2)'s literal factored numerator in Q[[x]]. Its factors are x, (1-x)^2, and (1-3x+x^2)^2.

**Definition 1.2 (Squared denominator of formula (2)).**

$$D: \mathbb{Q}[[x]], (D = (1 - 7 \cdot x + 13 \cdot x^{2} - 7 \cdot x^{3} + x^{4})^{2}).$$

*Formalization.* `D5/S3/Arith/RationalCompositionParityPeriodTen.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Proof: (definition). D is formula (2)'s literal squared quartic denominator in Q[[x]]. Squaring the quartic produces a degree-eight denominator with constant coefficient one.

**Theorem 1.3 (Denominator expansion).**

$$D = 1 - 14 \cdot x + 75 \cdot x^{2} - 196 \cdot x^{3} + 269 \cdot x^{4} - 196 \cdot x^{5} + 75 \cdot x^{6} - 14 \cdot x^{7} + x^{8}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.denominator_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalization: simp unfolds D and ring gives the nine coefficients. These coefficients determine the convolution formula for multiplying a power series by D.

**Theorem 1.4 (Numerator expansion).**

$$N = x - 8 \cdot x^{2} + 24 \cdot x^{3} - 34 \cdot x^{4} + 24 \cdot x^{5} - 8 \cdot x^{6} + x^{7}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.numerator_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalization: simp unfolds N and ring gives the eight initial coefficients. They supply the right-hand sides of the coefficient equations in degrees zero through seven.

**Definition 1.5 (The recurrence-defined integer sequence).**

$$a: \mathbb{N} \to \mathbb{Z}, (a\left(0\right) = 0 \land \left(a\left(1\right) = 1 \land \left(a\left(2\right) = 6 \land \left(a\left(3\right) = 33 \land \left(a\left(4\right) = 174 \land \left(a\left(5\right) = 892 \land \left(a\left(6\right) = 4480 \land \left(a\left(7\right) = 22149 \land \left(\forall n \in \mathbb{N},\; a\left(n + 8\right) = 14 \cdot a\left(n + 7\right) - 75 \cdot a\left(n + 6\right) + 196 \cdot a\left(n + 5\right) - 269 \cdot a\left(n + 4\right) + 196 \cdot a\left(n + 3\right) - 75 \cdot a\left(n + 2\right) + 14 \cdot a\left(n + 1\right) - a\left(n\right)\right)\right)\right)\right)\right)\right)\right)\right)).$$

*Formalization.* `D5/S3/Arith/RationalCompositionParityPeriodTen.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Proof: (definition). The sequence a is defined by the order-eight recurrence with its eight initial values; it is not stipulated by parity or by a finite table. Its later values are therefore determined uniquely from the preceding eight values.

**Theorem 1.6 (Homogeneous coefficient equations).**

$$\forall n \in \mathbb{N},\; a\left(n + 8\right) - 14 \cdot a\left(n + 7\right) + 75 \cdot a\left(n + 6\right) - 196 \cdot a\left(n + 5\right) + 269 \cdot a\left(n + 4\right) - 196 \cdot a\left(n + 3\right) + 75 \cdot a\left(n + 2\right) - 14 \cdot a\left(n + 1\right) + a\left(n\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.rational_tail_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof: linear normalization of the order-eight recurrence gives the coefficient equations above degree seven. Rearranging the recurrence places every term on the left and yields zero.

**Theorem 1.7 (Inhomogeneous coefficient equations).**

$$a\left(0\right) = 0 \land \left(a\left(1\right) - 14 \cdot a\left(0\right) = 1 \land \left(a\left(2\right) - 14 \cdot a\left(1\right) + 75 \cdot a\left(0\right) = -8 \land \left(a\left(3\right) - 14 \cdot a\left(2\right) + 75 \cdot a\left(1\right) - 196 \cdot a\left(0\right) = 24 \land \left(a\left(4\right) - 14 \cdot a\left(3\right) + 75 \cdot a\left(2\right) - 196 \cdot a\left(1\right) + 269 \cdot a\left(0\right) = -34 \land \left(a\left(5\right) - 14 \cdot a\left(4\right) + 75 \cdot a\left(3\right) - 196 \cdot a\left(2\right) + 269 \cdot a\left(1\right) - 196 \cdot a\left(0\right) = 24 \land \left(a\left(6\right) - 14 \cdot a\left(5\right) + 75 \cdot a\left(4\right) - 196 \cdot a\left(3\right) + 269 \cdot a\left(2\right) - 196 \cdot a\left(1\right) + 75 \cdot a\left(0\right) = -8 \land a\left(7\right) - 14 \cdot a\left(6\right) + 75 \cdot a\left(5\right) - 196 \cdot a\left(4\right) + 269 \cdot a\left(3\right) - 196 \cdot a\left(2\right) + 75 \cdot a\left(1\right) - 14 \cdot a\left(0\right) = 1\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.initial_coefficient_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof: norm_num substitutes the eight initial values into the convolution equations for multiplication by D. This gives the inhomogeneous coefficient equations in degrees zero through seven.

**Theorem 1.8 (Generating-function product identity).**

$$mk\left((n \mapsto cast\left(a\left(n\right), \mathbb{Q}\right))\right) \cdot (1 - 7 \cdot x + 13 \cdot x^{2} - 7 \cdot x^{3} + x^{4})^{2} = x \cdot (1 - x)^{2} \cdot (1 - 3 \cdot x + x^{2})^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.generating_function_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof: coefficient extensionality reduces the power-series identity to equality in each degree. The recurrence supplies the homogeneous tail equations above degree seven, while the eight initial equations and the expansions of D and N settle degrees zero through seven.

**Theorem 1.9 (Generating function in division form).**

$$mk\left((n \mapsto cast\left(a\left(n\right), \mathbb{Q}\right))\right) = x \cdot (1 - x)^{2} \cdot (1 - 3 \cdot x + x^{2})^{2} \cdot ((1 - 7 \cdot x + 13 \cdot x^{2} - 7 \cdot x^{3} + x^{4})^{2})^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.generating_function` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof: power-series inversion rewrites the product identity, and the expanded denominator proves its constant coefficient is one. Consequently D is invertible and A(x)D(x)=N(x) becomes A(x)=N(x)D(x)^-1.

**Theorem 1.10 (Formula (2) uniquely determines its integer coefficients).**

$$\forall b \in \mathbb{N} \to \mathbb{Z},\; (mk\left((n \mapsto cast\left(b\left(n\right), \mathbb{Q}\right))\right) \cdot (1 - 7 \cdot x + 13 \cdot x^{2} - 7 \cdot x^{3} + x^{4})^{2} = x \cdot (1 - x)^{2} \cdot (1 - 3 \cdot x + x^{2})^{2}) \Rightarrow \left(\forall n \in \mathbb{N},\; b\left(n\right) = a\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.coefficients_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof: comparing coefficients in b(x)D(x)=N(x) and a(x)D(x)=N(x) gives the same convolution equation for b and a. Strong induction, using equality of earlier coefficients and the constant coefficient one of D, gives b(n)=a(n) for every n.

**Theorem 1.11 (Characteristic-two recurrence).**

$$\forall n \in \mathbb{N},\; cast\left(a\left(n + 8\right), ZMod\left(2\right)\right) = cast\left(a\left(n\right), ZMod\left(2\right)\right) + cast\left(a\left(n + 2\right), ZMod\left(2\right)\right) + cast\left(a\left(n + 4\right), ZMod\left(2\right)\right) + cast\left(a\left(n + 6\right), ZMod\left(2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.reduced_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof: casting the integer recurrence to characteristic two makes the coefficients 14 and 196 vanish and makes 75 and 269 equal one. Since negation is the identity, the surviving terms are exactly the four even lags.

**Theorem 1.12 (Period ten modulo two).**

$$\forall n \in \mathbb{N},\; cast\left(a\left(n + 10\right), ZMod\left(2\right)\right) = cast\left(a\left(n\right), ZMod\left(2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.parity_period_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof: two shifted reduced recurrences cancel in characteristic two. Substituting the recurrence at n into the one at n+2 makes every intermediate term occur twice, leaving a(n+10)=a(n).

**Theorem 1.13 (Odd values exactly in four residue classes).**

$$\forall n \in \mathbb{N},\; Odd\left(a\left(n\right)\right) \Leftrightarrow n \bmod 10 \in \left\{1, 3, 7, 9\right\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.odd_iff_mod_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof: period ten reduces every index to one of the first ten residues. Direct evaluation of those ten values gives odd terms precisely at residues 1, 3, 7, and 9.

**Theorem 1.14 (Parity for the formula (2) coefficient sequence).**

$$\forall b \in \mathbb{N} \to \mathbb{Z},\; (mk\left((n \mapsto cast\left(b\left(n\right), \mathbb{Q}\right))\right) \cdot (1 - 7 \cdot x + 13 \cdot x^{2} - 7 \cdot x^{3} + x^{4})^{2} = x \cdot (1 - x)^{2} \cdot (1 - 3 \cdot x + x^{2})^{2}) \Rightarrow \left(\forall n \in \mathbb{N},\; Odd\left(b\left(n\right)\right) \Leftrightarrow n \bmod 10 \in \left\{1, 3, 7, 9\right\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.odd_iff_mod_ten_of_generating_function` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof: coefficients_unique rewrites the sequence and the period-ten residue theorem closes the result. Thus every integer coefficient sequence satisfying formula (2) has the same parity pattern.

**Theorem 1.15 (Even values at positive even indices).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow Even\left(a\left(2 \cdot n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.even_at_even_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof: modular arithmetic projects the first OEIS conjecture from the residue characterization. An even index has an even residue modulo ten, so it never lies in the four odd residue classes.

**Theorem 1.16 (Even values at odd indices).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(Even\left(a\left(2 \cdot n - 1\right)\right) \Leftrightarrow \left(\exists k \in \mathbb{N},\; 1 \le k \land n = 5 \cdot k - 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.even_at_odd_index_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof: modular arithmetic projects the second OEIS conjecture from the residue characterization. Natural subtraction is truncated at zero. For n at least one, a(2n-1) is even exactly when n is congruent to 3 modulo 5, equivalently n=5k-2 for some k at least one.

**Theorem 1.17 (First conjecture for formula (2) coefficients).**

$$\forall b \in \mathbb{N} \to \mathbb{Z},\; (mk\left((n \mapsto cast\left(b\left(n\right), \mathbb{Q}\right))\right) \cdot (1 - 7 \cdot x + 13 \cdot x^{2} - 7 \cdot x^{3} + x^{4})^{2} = x \cdot (1 - x)^{2} \cdot (1 - 3 \cdot x + x^{2})^{2}) \Rightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow Even\left(b\left(2 \cdot n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.even_at_even_index_of_generating_function` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof: coefficient uniqueness gives b(2n)=a(2n), and the even-index result for a then proves that b(2n) is even.

**Theorem 1.18 (Second conjecture for formula (2) coefficients).**

$$\forall b \in \mathbb{N} \to \mathbb{Z},\; (mk\left((n \mapsto cast\left(b\left(n\right), \mathbb{Q}\right))\right) \cdot (1 - 7 \cdot x + 13 \cdot x^{2} - 7 \cdot x^{3} + x^{4})^{2} = x \cdot (1 - x)^{2} \cdot (1 - 3 \cdot x + x^{2})^{2}) \Rightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(Even\left(b\left(2 \cdot n - 1\right)\right) \Leftrightarrow \left(\exists k \in \mathbb{N},\; 1 \le k \land n = 5 \cdot k - 2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/RationalCompositionParityPeriodTen.even_at_odd_index_iff_of_generating_function` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Proof: coefficient uniqueness gives b(2n-1)=a(2n-1), so the odd-index characterization for a transfers the stated equivalence to b.

**Definition 1.19 (Basic rational-function map).**

$$\forall y \in \mathbb{Q}(x),\; Bf\left(y\right) = \frac{y}{(1 - y)^{2}}$$

*Formalization.* `D5/S3/Arith/RationalCompositionParityPeriodTen.Bf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Proof: (definition). OEIS A396093 states B(x)=x/(1-x)^2. Here Bf is that total field operation on Q(x). Thus Bf(y) is defined for every rational function y, including when 1-y is zero.

The sequence a is defined by the order-eight recurrence with its eight initial values; Theorem generating_function identifies it with the coefficient sequence of formula (2), Theorem coefficients_unique shows formula (2) determines it, and direct rational-function normalization identifies formula (2) with B(B(B(x))) in Q(x). The three together tie a to the OEIS definition.

## References

- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.Bf`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.D`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.N`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.a`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.coefficients_unique`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.denominator_expansion`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.even_at_even_index`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.even_at_even_index_of_generating_function`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.even_at_odd_index_iff`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.even_at_odd_index_iff_of_generating_function`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.generating_function`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.generating_function_identity`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.initial_coefficient_equations`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.numerator_expansion`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.odd_iff_mod_ten`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.odd_iff_mod_ten_of_generating_function`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.parity_period_ten`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.rational_tail_equation`
- Truth anchor: `D5/S3/Arith/RationalCompositionParityPeriodTen.reduced_recurrence`
