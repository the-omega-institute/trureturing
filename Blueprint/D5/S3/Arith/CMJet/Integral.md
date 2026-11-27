# The integral inert operator and the complete jet row

## Abstract

The p-fold derivative at an inert prime is p times an integral linear endomorphism. Repeated blocks give an integral factorization of all jets and a divisor of the content of the complete row.

**Lemma 1.1 (Coefficient reduction respects iteration).**

Lean statement: `D5/S3/Arith/CMJet/Integral.reduce_iter`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Integral.reduce_iter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reducing both components modulo p commutes with the derivation, hence with each iterate of every order.

**Definition 1.2 (The integral quotient endomorphism).**

Lean statement: `D5/S3/Arith/CMJet/Integral.inertLift`

*Formalization.* `D5/S3/Arith/CMJet/Integral.inertLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a prime p ≡ 3 modulo 4, the pointwise quotient of D^p by p exists by reduction and is unique by torsion-freeness of the integral polynomial pairs. Uniqueness gives linearity over the integers.

**Theorem 1.3 (Exact integral factorization of iterates).**

Lean statement: `D5/S3/Arith/CMJet/Integral.iter_eq_inertLift`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Integral.iter_eq_inertLift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write N = p q + r with q = N div p and r = N mod p. On every integral pair, D^N acts as p^q times q applications of the integral quotient to D^r of the input.

**Theorem 1.4 (Divisibility of every evaluated jet).**

Lean statement: `D5/S3/Arith/CMJet/Integral.inert_dvd_jet`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Integral.inert_dvd_jet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Levent Alpöge (2026). *Riemann hypothesis formalization in Lean*. URL: <https://github.com/the-omega-institute/riemann-hypothesis>.

*Commentary.*

For each inert prime p and every natural order N, the evaluated derivative of every integral polynomial pair at the base point is divisible by p^(N div p).

**Definition 1.5 (The complete row).**

Lean statement: `D5/S3/Arith/CMJet/Integral.row`

*Formalization.* `D5/S3/Arith/CMJet/Integral.row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At order N = 4m+1, the row reads the jets of X^(4j+1) for 0 ≤ j ≤ m.

**Theorem 1.6 (Vanishing outside the row).**

Lean statement: `D5/S3/Arith/CMJet/Integral.jet_monomial_outside_row`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Integral.jet_monomial_outside_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pure monomial of exponent greater than N or outside the class one modulo four has zero evaluated jet at order N.

**Theorem 1.7 (The last column is N!).**

Lean statement: `D5/S3/Arith/CMJet/Integral.row_last`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Integral.row_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The final exponent is N, so the factorial highest-monomial rule gives N! for the last entry.

**Theorem 1.8 (An inert prime power divides the row content).**

Lean statement: `D5/S3/Arith/CMJet/Integral.inert_dvd_content`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CMJet/Integral.inert_dvd_content` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every entry is divisible by p^(N div p), hence so is the gcd of their absolute values. The nonzero last entry also ensures positive content dividing N!.

## References

- Truth anchor: `D5/S3/Arith/CMJet/Integral.inertLift`
- Truth anchor: `D5/S3/Arith/CMJet/Integral.inert_dvd_content`
- Truth anchor: `D5/S3/Arith/CMJet/Integral.inert_dvd_jet`
- Truth anchor: `D5/S3/Arith/CMJet/Integral.iter_eq_inertLift`
- Truth anchor: `D5/S3/Arith/CMJet/Integral.jet_monomial_outside_row`
- Truth anchor: `D5/S3/Arith/CMJet/Integral.reduce_iter`
- Truth anchor: `D5/S3/Arith/CMJet/Integral.row`
- Truth anchor: `D5/S3/Arith/CMJet/Integral.row_last`
- Dependency: [D5/S3/Arith/CMJet/Prime](Prime.md)
