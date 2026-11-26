# Pair sums of polynomial roots

## Abstract

The pair-sum resultant converts half-plane stability to integer coefficient signs.

**Definition 1.1 (Pair-sum resultant).**

$$r\left(T\right)=\operatorname{Res}_{Y}\left(p\left(Y\right), p\left(T-Y\right)\right)$$

*Formalization.* `D5/S3/Analytic/Polynomial/PairSumStability.sumResultant` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. V. Brawley and L. Carlitz (1987). *Irreducibles and the composed product for polynomials over a finite field*. DOI: [10.1016/0012-365X(87)90135-X](https://doi.org/10.1016/0012-365X(87)90135-X).

*Commentary.*

Use Y as the eliminated variable and T as the coefficient variable. Both degree parameters are the degree of p.

**Theorem 1.2 (Roots are pair sums).**

$$r\left(z\right)=0\iff\exists u,v, (p\left(u\right)=0\land p\left(v\right)=0\land u+v=z)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/PairSumStability.eval2_sumResultant_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. V. Brawley and L. Carlitz (1987). *Irreducibles and the composed product for polynomials over a finite field*. DOI: [10.1016/0012-365X(87)90135-X](https://doi.org/10.1016/0012-365X(87)90135-X).

*Commentary.*

For a nonzero polynomial and an injective coefficient map to the complex numbers, evaluation commutes with the Sylvester determinant. Its product formula permits equal roots in the pair.

**Theorem 1.3 (Degree and leading coefficient).**

$$\operatorname{deg}\left(r\right)=d^{2}\land\operatorname{lc}\left(r\right)=a^{2d}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/PairSumStability.sumResultant_degree_leading` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. V. Brawley and L. Carlitz (1987). *Irreducibles and the composed product for polynomials over a finite field*. DOI: [10.1016/0012-365X(87)90135-X](https://doi.org/10.1016/0012-365X(87)90135-X).

*Commentary.*

Under an injective coefficient map to the complex numbers, let d be the degree of the nonzero input and a its leading coefficient. The product of the d translated factors has degree d², with another factor a^d from the resultant formula.

**Theorem 1.4 (Closed stability).**

$$(\forall z\in\mathbb{C}, p\left(z\right)=0\implies\Re z\le0)\iff(\forall 0\le j\le\operatorname{deg}\left(p\right)^{2}, 0\le[T^{j}]r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/PairSumStability.closed_iff_sumResultant_coeff_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. V. Brawley and L. Carlitz (1987). *Irreducibles and the composed product for polynomials over a finite field*. DOI: [10.1016/0012-365X(87)90135-X](https://doi.org/10.1016/0012-365X(87)90135-X).

*Commentary.*

Here p has integer coefficients and positive leading coefficient. Real linear factors and conjugate quadratics give nonnegative coefficients for a closed-stable resultant. Any root of p with positive real part pairs with its conjugate to give a positive real resultant root, which the coefficient signs exclude.

**Theorem 1.5 (Strict stability).**

$$(\forall z\in\mathbb{C}, p\left(z\right)=0\implies\Re z<0)\iff((\forall 0\le j\le\operatorname{deg}\left(p\right)^{2}, 0\le[T^{j}]r)\land0<[T^{0}]r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/PairSumStability.strict_iff_sumResultant_coeff_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. V. Brawley and L. Carlitz (1987). *Irreducibles and the composed product for polynomials over a finite field*. DOI: [10.1016/0012-365X(87)90135-X](https://doi.org/10.1016/0012-365X(87)90135-X).

*Commentary.*

For integer p with positive leading coefficient, the same scan and a positive constant coefficient exclude pair sums equal to zero. An imaginary-axis root of p pairs with its conjugate at zero.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/PairSumStability.closed_iff_sumResultant_coeff_nonneg`
- Truth anchor: `D5/S3/Analytic/Polynomial/PairSumStability.eval2_sumResultant_eq_zero_iff`
- Truth anchor: `D5/S3/Analytic/Polynomial/PairSumStability.strict_iff_sumResultant_coeff_nonneg`
- Truth anchor: `D5/S3/Analytic/Polynomial/PairSumStability.sumResultant`
- Truth anchor: `D5/S3/Analytic/Polynomial/PairSumStability.sumResultant_degree_leading`
