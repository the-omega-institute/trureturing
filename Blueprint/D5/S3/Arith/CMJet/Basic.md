# Lemniscatic polynomial pairs and their derivatives

## Abstract

The invariant derivation on the polynomial-pair algebra gives a three-term fourth derivative and controls the support and highest monomial of each odd jet.

**Definition 1.1 (Polynomial pairs).**

Lean statement: `D5/S3/Arith/CMJet/Basic.Curve`

*Formalization.* `D5/S3/Arith/CMJet/Basic.Curve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Over any commutative ring A, the carrier is the free A[X]-module on 1 and Y. Multiplication uses the relation Y² = 1 − X⁴.

**Lemma 1.2 (The curve relation).**

Lean statement: `D5/S3/Arith/CMJet/Basic.y_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Basic.y_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square of Y is the pure polynomial 1 − X⁴. This is the relation used to identify the restricted derivation in prime characteristic.

**Definition 1.3 (The invariant derivation).**

Lean statement: `D5/S3/Arith/CMJet/Basic.D`

*Formalization.* `D5/S3/Arith/CMJet/Basic.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On f + Yg the operator has polynomial part (1 − X⁴)g′ − 2X³g and Y-part f′. Differentiating the pair multiplication proves the Leibniz law over A.

**Lemma 1.4 (The square on pure polynomials).**

Lean statement: `D5/S3/Arith/CMJet/Basic.iter_two_poly`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Basic.iter_two_poly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two applications of D send f to the pure polynomial Qf = (1 − X⁴)f″ − 2X³f′.

**Lemma 1.5 (The two-term monomial rule).**

Lean statement: `D5/S3/Arith/CMJet/Basic.Q_X_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Basic.Q_X_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two terms of Q(X^k) have exponents k−2 and k+2 and coefficients k(k−1) and −k(k+1). The first coefficient vanishes at k equal to zero or one.

**Lemma 1.6 (The three-term fourth derivative).**

Lean statement: `D5/S3/Arith/CMJet/Basic.iter_four_X_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Basic.iter_four_X_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three exponents are k−4, k and k+4. Their coefficients are k(k−1)(k−2)(k−3), −2k²(k²+5) and k(k+1)(k+2)(k+3). When k < 4, the coefficient of the term with truncated subtraction is zero.

**Lemma 1.7 (Support modulo four).**

Lean statement: `D5/S3/Arith/CMJet/Basic.Q_iter_monomial_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Basic.Q_iter_monomial_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After s applications of Q to X^r, a nonzero coefficient of degree n requires n ≡ 2s+r modulo four.

**Definition 1.8 (Evaluation at the base point).**

Lean statement: `D5/S3/Arith/CMJet/Basic.atO`

*Formalization.* `D5/S3/Arith/CMJet/Basic.atO` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluation at X = 0 and Y = 1 adds the constant coefficients of both polynomial components.

**Theorem 1.9 (The factorial at the highest monomial).**

Lean statement: `D5/S3/Arith/CMJet/Basic.odd_top_jet`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Basic.odd_top_jet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At order 2s+1, the value of the derivative of X^(2s+1) at the base point is (2s+1)!. Only the descending term of Q can contribute to the coefficient of X in each step toward the lowest degree.

## References

- Truth anchor: `D5/S3/Arith/CMJet/Basic.Curve`
- Truth anchor: `D5/S3/Arith/CMJet/Basic.D`
- Truth anchor: `D5/S3/Arith/CMJet/Basic.Q_X_pow`
- Truth anchor: `D5/S3/Arith/CMJet/Basic.Q_iter_monomial_support`
- Truth anchor: `D5/S3/Arith/CMJet/Basic.atO`
- Truth anchor: `D5/S3/Arith/CMJet/Basic.iter_four_X_pow`
- Truth anchor: `D5/S3/Arith/CMJet/Basic.iter_two_poly`
- Truth anchor: `D5/S3/Arith/CMJet/Basic.odd_top_jet`
- Truth anchor: `D5/S3/Arith/CMJet/Basic.y_sq`
