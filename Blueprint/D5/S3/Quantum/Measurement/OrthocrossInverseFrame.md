# Geometric parameters for the orthocross inverse

## Abstract

The standard orthocross frame has diagonal d, upper entry a = (1-i)/2 and lower entry b = (1+i)/2. A geometric ratio and a nonzero denominator specify its proposed inverse entries.

**Definition 1.1 (Upper frame entry).**

$$a = \frac{1-i}{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.upperEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper frame entry is defined by this equality.

**Definition 1.2 (Lower frame entry).**

$$b = \frac{1+i}{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.lowerEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lower frame entry is defined by this equality.

**Definition 1.3 (Complex scale).**

$$\forall d, L = d-a$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.scale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex scale is defined by this equality.

**Definition 1.4 (Geometric ratio).**

$$\forall d, q = \frac{d-b}{L}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.ratio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The geometric ratio is defined by this equality.

**Definition 1.5 (Geometric denominator).**

$$\forall d, \Delta = b-aq^{d}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.denominator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The geometric denominator is defined by this equality.

**Definition 1.6 (Upper inverse coefficient).**

$$\forall d, u = \frac{-iaq^{d-2}}{L^{2}\Delta}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.upperConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper inverse coefficient is defined by this equality.

**Definition 1.7 (Diagonal inverse coefficient).**

$$\forall d, t = \frac{1}{L}-\frac{iaq^{d-1}}{L^{2}\Delta}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.diagonalConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal inverse coefficient is defined by this equality.

**Definition 1.8 (Hermitian triangular candidate).**

$$\forall d, \forall j, k, (j = k \Rightarrow M_{jk} = t) \land (j < k \Rightarrow M_{jk} = uq^{j-k+1}) \land (k < j \Rightarrow M_{jk} = (uq^{k-j+1})^{*})$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.candidate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For indices j,k in Fin d, the candidate has diagonal t, entry u q^(j-k+1) above the diagonal, and the conjugate of the corresponding upper entry below the diagonal. Integer exponents are used.

**Theorem 1.9 (The ratio is nonzero).**

$$\forall d, q \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.ratio_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scale has imaginary part one half, so it and its conjugate are nonzero.

**Theorem 1.10 (The ratio is distinct from one).**

$$\forall d, q \neq 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.ratio_ne_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The difference q-1 equals -i divided by the nonzero scale.

**Theorem 1.11 (Unit modulus).**

$$\forall d, \Vert q\Vert = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.norm_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerator is the conjugate of L. Its norm equals the nonzero norm of L.

**Theorem 1.12 (Conjugation inverts the ratio).**

$$\forall d, q^{*} = q^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.star_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating the quotient interchanges its numerator and denominator.

**Theorem 1.13 (Nonzero denominator).**

$$\forall d, d > 0 \Rightarrow \Delta \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.denominator_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A zero denominator would imply q^d = i. For d at least two, the telescoping bound |q^d-1| <= d |q-1|, together with |L|^2 = d^2-d+1/2, contradicts |i-1|^2 = 2. Dimension one is evaluated exactly.

**Theorem 1.14 (Nonzero upper coefficient).**

$$\forall d, d > 0 \Rightarrow u \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.upperConstant_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All factors in the numerator and denominator of u are nonzero in positive dimension.

**Theorem 1.15 (The candidate inverts the frame).**

$$\forall d, d > 0 \Rightarrow \omega M = I$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.frame_mul_candidate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Scale the candidate by L^2 delta. The geometric column sum is i L q^(d-k-1), which gives the first product row. Subtracting adjacent frame rows leaves only two entries, and the geometric recurrence gives the difference of the corresponding identity rows. Induction gives every row.

**Theorem 1.16 (Closed inverse form).**

$$\forall d, d > 0 \Rightarrow \omega^{-1} = M$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.inverse_frame_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A right inverse of a square matrix equals its nonsingular inverse. Hermiticity identifies the lower entries with the conjugates of the upper entries.

**Theorem 1.17 (Positive real diagonal).**

$$\forall d, d > 0 \Rightarrow 0 < t$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.diagonalConstant_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The standard frame is positive definite, and so is its inverse. Every diagonal entry of the inverse is therefore a strictly positive real number.

**Theorem 1.18 (Conjugate coefficient phase).**

$$\forall d, u^{*} = uiq^{2-d}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.upperConstant_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating delta gives -delta q^(-d), while conjugating L gives qL. The factors in the conjugate of u therefore cancel to a/(L^2 delta).

**Theorem 1.19 (A short quotient for the diagonal ratio).**

$$\forall d, d > 0 \Rightarrow \frac{t}{u} = \frac{q-iq^{2-d}}{1-q}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.diagonal_div_upperConstant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identities t = 1/L + qu and qt - conjugate(u) = 1/L give t(1-q) = qu - conjugate(u). Substituting the coefficient phase yields the quotient.

**Theorem 1.20 (Small Gaussian polynomials do not vanish).**

$$\forall d, \forall p, p \neq 0 \land (\forall n, \Vert p_{n}\Vert^{2} < 2d^{2}-2d+1) \Rightarrow p(q) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.polynomial_at_ratio_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial p has Gaussian-integer coefficients. Their Gaussian norm is the squared complex modulus. Write q=A/B with A=(d-1)-di and B=d-(d-1)i. An explicit Bezout identity makes A and B coprime. Scaling polynomial roots by B shows that a root at q would force B to divide the nonzero leading coefficient. Its norm would then be at least norm(B)=2d^2-2d+1, a contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.candidate`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.denominator`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.denominator_ne_zero`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.diagonalConstant`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.diagonalConstant_pos`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.diagonal_div_upperConstant`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.frame_mul_candidate`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.inverse_frame_eq`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.lowerEntry`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.norm_ratio`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.polynomial_at_ratio_ne_zero`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.ratio`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.ratio_ne_one`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.ratio_ne_zero`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.scale`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.star_ratio`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.upperConstant`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.upperConstant_ne_zero`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.upperConstant_phase`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossInverseFrame.upperEntry`
- Dependency: [D5/S3/AnalyticClosure/ComplexPowerDifference](../../AnalyticClosure/ComplexPowerDifference.md)
- Dependency: [D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger](OrthocrossGramHalfInteger.md)
