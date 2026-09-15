# The Lerch Recurrence and the Somos Constant

## Abstract

The Lerch convolution source, its summability and unique existence, and its limit at the Somos constant.

**Definition 1.1 (The Lerch kernel at one half).**

$$\forall s:\mathbb{N}, \operatorname{LerchKernel}\left(s\right)=\sum'_{j:\mathbb{N}} \frac{\left(\frac{1}{2}:\mathbb{R}\right)^{j}}{\left(\left(j:\mathbb{R}\right)+1\right)^{s}}$$

*Formalization.* `D5/S1/Recurrence/LerchSomosLimit.LerchKernel` (`✓ std3`).

*Citation.* Eric W. Weisstein (2026). *Lerch Transcendent*. URL: <https://mathworld.wolfram.com/LerchTranscendent.html>.

*Commentary.*

The classical Lerch series at first argument one half and third argument one defines a real kernel for every natural exponent. Equation (1) of the source gives the series, and equation (6) identifies its normalization as twice the polylogarithm at one half. The summation index starts at zero.

**Definition 1.2 (The real Somos constant).**

$$\operatorname{SomosConstant}=\operatorname{Real}.\operatorname{exp}\left(\sum'_{j:\mathbb{N}} \frac{\operatorname{Real}.\operatorname{log}\left(\left(j:\mathbb{R}\right)+1\right)}{\left(2:\mathbb{R}\right)^{j+1}}\right)$$

*Formalization.* `D5/S1/Recurrence/LerchSomosLimit.SomosConstant` (`✓ std3`).

*Citation.* Johannes W. Meijer (2016). *OEIS A112302, Lerch recurrence limit conjecture*. URL: <https://oeis.org/A112302>.

*Commentary.*

The exponential of this logarithmic sum specifies the real constant whose decimal expansion is A112302. The zero-indexed expression includes the vanishing logarithm of one. The entry's FORMULA section gives the logarithmic expression and the infinite product as published identities.

**Definition 1.3 (The initial value and linear convolution recurrence).**

$$\forall a:\mathbb{N}\to\mathbb{R}, \operatorname{LPSource}\left(a\right)\iff\left(a\left(0\right)=1 \land \left(\forall n:\mathbb{N}, 0<n\implies a\left(n\right)=\frac{1}{\left(n:\mathbb{R}\right)}\cdot \sum_{k:\operatorname{Fin} n} \operatorname{LerchKernel}\left(n-k.\mathrm{val}\right)\cdot a\left(k.\mathrm{val}\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/LerchSomosLimit.LPSource` (`✓ std3`).

*Citation.* Johannes W. Meijer (2016). *OEIS A112302, Lerch recurrence limit conjecture*. URL: <https://oeis.org/A112302>.

*Commentary.*

The initial value is one. At each positive natural index, the recurrence uses every preceding index exactly once. A finite index k has natural value k.val strictly below n, so the kernel exponent is positive. All scalar arithmetic and sequence values are real; the subtraction in the kernel exponent is natural subtraction. This is the LP recurrence in the conjecture's COMMENTS paragraph.

**Theorem 1.4 (Summability, unique source, and the Somos limit).**

$$\left(\forall s:\mathbb{N}, 0<s\implies \operatorname{Summable}\left(j:\mathbb{N}\mapsto\frac{\left(\frac{1}{2}:\mathbb{R}\right)^{j}}{\left(\left(j:\mathbb{R}\right)+1\right)^{s}}\right)\right) \land \left(\operatorname{Summable}\left(j:\mathbb{N}\mapsto\frac{\operatorname{Real}.\operatorname{log}\left(\left(j:\mathbb{R}\right)+1\right)}{\left(2:\mathbb{R}\right)^{j+1}}\right) \land \left(\left(\exists! a:\mathbb{N}\to\mathbb{R}, \operatorname{LPSource}\left(a\right)\right) \land \left(\forall a:\mathbb{N}\to\mathbb{R}, \operatorname{LPSource}\left(a\right)\implies \operatorname{Filter}.\operatorname{Tendsto}\left(a,\operatorname{Filter}.\operatorname{atTop},\operatorname{nhds}\left(\operatorname{SomosConstant}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/LerchSomosLimit.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a112302-lerch-somos-limit` (proved) by `D5/S1/Recurrence/LerchSomosLimit.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a112302-lerch-somos-limit","declaration_gid":"D5/S1/Recurrence/LerchSomosLimit.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Johannes W. Meijer (2016). *OEIS A112302, Lerch recurrence limit conjecture*. URL: <https://oeis.org/A112302>.

*Acknowledgement.* Eric W. Weisstein (2026). *Lerch Transcendent*. URL: <https://mathworld.wolfram.com/LerchTranscendent.html>.

*Acknowledgement.* Mark W. Coffey (2015). *Integral representations of functions and Addison-type series for mathematical constants*. DOI: [10.1016/j.jnt.2015.04.005](https://doi.org/10.1016/j.jnt.2015.04.005). URL: <https://arxiv.org/abs/1006.2551v1>.

*Commentary.*

The statement has four conjuncts: summability of the kernel series at every positive natural exponent, summability of the logarithmic constant series, unique existence of a total real sequence satisfying the initial value and recurrence, and convergence of every such sequence to the specified real constant.

The limit uses the atTop filter on the natural numbers and the real neighborhood filter. Thus every positive real tolerance must hold at all sufficiently large natural indices. The two summability clauses give the infinite sums their convergent-series meaning, and the unique-existence clause supplies the source sequence.

The proof constructs the source by strong recursion. Subtracting one from the kernel gives an exponentially bounded nonnegative sequence; its convolution defines nonnegative coefficients bounded by two to the negative index. Their partial sums satisfy the original LP recurrence and hence converge. Differentiating the associated convergent power series identifies the coefficient sum with an exponential. An absolutely summable double series and a weighted logarithmic telescoping sum identify its exponent with the Somos series. This last constant identity is known from Coffey, Proposition 5(b), equation (1.25), specialized to t equal to two.

## References

- Truth anchor: `D5/S1/Recurrence/LerchSomosLimit.LPSource`
- Truth anchor: `D5/S1/Recurrence/LerchSomosLimit.LerchKernel`
- Truth anchor: `D5/S1/Recurrence/LerchSomosLimit.SomosConstant`
- Truth anchor: `D5/S1/Recurrence/LerchSomosLimit.result`
