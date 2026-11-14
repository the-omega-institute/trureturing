# The six cubic least remainders

## Abstract

All six branches of Englander Conjecture XIV hold for the exact quotient at every integer index greater than two.

**Definition 1.1 (The six prescribed polynomials).**

$$\forall n \in \mathbb{N},\; ((((((\operatorname{mod}\left(n, 6\right) = 0) \Rightarrow (\operatorname{twiceR}\left(n\right) = ((n: \mathbb{Z}))^{3}+((n: \mathbb{Z}))^{2}-(n: \mathbb{Z}))) \land ((\operatorname{mod}\left(n, 6\right) = 1) \Rightarrow (\operatorname{twiceR}\left(n\right) = ((n: \mathbb{Z}))^{3}-2*((n: \mathbb{Z}))^{2}+2*(n: \mathbb{Z})-1))) \land ((\operatorname{mod}\left(n, 6\right) = 2) \Rightarrow (\operatorname{twiceR}\left(n\right) = ((n: \mathbb{Z}))^{3}+3*((n: \mathbb{Z}))^{2}-(n: \mathbb{Z})-2))) \land ((\operatorname{mod}\left(n, 6\right) = 3) \Rightarrow (\operatorname{twiceR}\left(n\right) = ((n: \mathbb{Z}))^{3}-2*((n: \mathbb{Z}))^{2}+1))) \land ((\operatorname{mod}\left(n, 6\right) = 4) \Rightarrow (\operatorname{twiceR}\left(n\right) = ((n: \mathbb{Z}))^{3}+((n: \mathbb{Z}))^{2}+(n: \mathbb{Z})-2))) \land ((\operatorname{mod}\left(n, 6\right) = 5) \Rightarrow (\operatorname{twiceR}\left(n\right) = ((n: \mathbb{Z}))^{3}-1))$$

*Formalization.* `D5/S3/Arith/Congruence/SelfPowerCubicRemainders.twiceR` (`✓ std3`).

*Citation.* Mathew Englander (2020). *Comments on OEIS A081215*. URL: <https://oeis.org/A081215/a081215.pdf>.

*Commentary.*

The branch is selected by the natural residue n modulo six. Every displayed polynomial is evaluated in the integers. These are exactly twice the remainders on physical page 63; using twice the remainder keeps integrality explicit.

**Theorem 1.2 (Uniform weighted-sum descent).**

$$\forall h \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall y \in \mathbb{Z},\; (y)^{3}+1 \mid (\operatorname{tail}\left(6*h+t, y\right)-(3*(h: \mathbb{Z})*(1+y+(y)^{2})+\operatorname{tail}\left(t, y\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/SelfPowerCubicRemainders.tail_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathew Englander (2020). *Comments on OEIS A081215*. URL: <https://oeis.org/A081215/a081215.pdf>.

*Commentary.*

Split the finite double sum into two consecutive blocks. For Q=y^3+1 and S=1+y+y^2, the six-step difference T(m+6,y)-T(m,y)-3S is divisible by Q. Induction gives the displayed statement for every h, t and integer y, without a restriction on t. This is the unbounded step used by the residue proof.

**Definition 1.3 (The full cubic claim).**

$$(\operatorname{claim}\left(\right)) \Leftrightarrow (\forall n \in \mathbb{N},\; (2 < n) \Rightarrow ((((n: \mathbb{Z})+1)^{2}*\operatorname{a}\left(n\right) = \operatorname{numerator}\left(n\right)) \land (2*\operatorname{emod}\left(\operatorname{a}\left(n\right), ((n: \mathbb{Z}))^{3}-1\right) = \operatorname{twiceR}\left(n\right))))$$

*Formalization.* `D5/S3/Arith/Congruence/SelfPowerCubicRemainders.claim` (`✓ std3`).

*Citation.* Mathew Englander (2020). *Comments on OEIS A081215*. URL: <https://oeis.org/A081215/a081215.pdf>.

*Commentary.*

Both conjuncts apply for every natural n greater than two. The first establishes the exact original quotient; the second identifies twice its least nonnegative integer remainder modulo n cubed minus one. This is equivalent to the printed integer domain and all six branch equalities.

**Theorem 1.4 (All six least-remainder branches).**

$$\forall n \in \mathbb{N},\; (2 < n) \Rightarrow ((((n: \mathbb{Z})+1)^{2}*\operatorname{a}\left(n\right) = \operatorname{numerator}\left(n\right)) \land (2*\operatorname{emod}\left(\operatorname{a}\left(n\right), ((n: \mathbb{Z}))^{3}-1\right) = \operatorname{twiceR}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/SelfPowerCubicRemainders.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mathew Englander (2020). *Comments on OEIS A081215*. URL: <https://oeis.org/A081215/a081215.pdf>.

*Commentary.*

Write n=6h+c with 0<=c<6. Apply the block descent at t=c+1 and y=-n. The six integral representatives are 108h^3+18h^2-3h, 108h^3+18h^2+3h, 108h^3+162h^2+69h+8, 108h^3+126h^2+45h+5, 108h^3+234h^2+171h+41 and 108h^3+270h^2+225h+62. The proof shows directly that the quotient minus the representative is divisible by the modulus, and that the representative lies in the half-open interval from zero to the modulus. Uniqueness of Euclidean remainder then applies. Polynomial expansion gives twiceR. No division by two in a residue ring or coprimality assumption is used.

## References

- Truth anchor: `D5/S3/Arith/Congruence/SelfPowerCubicRemainders.claim`
- Truth anchor: `D5/S3/Arith/Congruence/SelfPowerCubicRemainders.result`
- Truth anchor: `D5/S3/Arith/Congruence/SelfPowerCubicRemainders.tail_blocks`
- Truth anchor: `D5/S3/Arith/Congruence/SelfPowerCubicRemainders.twiceR`
- Dependency: [D5/S3/Arith/Congruence/SelfPowerQuotient](SelfPowerQuotient.md)
