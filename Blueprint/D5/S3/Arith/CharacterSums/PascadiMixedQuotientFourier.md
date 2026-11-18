# Completion in the two digits

## Abstract

Complete Fourier coefficients on the mixed quotient of the Pascadi inverse graph.

**Theorem 1.1 (Exact stationary sum at arbitrary frequencies).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMixedQuotientFourier.coefficient_eq_stationary_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMixedQuotientFourier.coefficient_eq_stationary_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be prime. Fix a unit C modulo p squared. The graph sends the unit x modulo p squared and the digit s modulo p to C/x modulo p squared and C*s/x squared modulo p. Its complete coefficient uses the two standard complex additive characters with frequencies A,B modulo p squared and D,E modulo p.

Write x as the canonical lift of its unit residue a plus p*j with j modulo p. The inverse changes by minus p*j times the squared inverse of the canonical lift, since the square of p*j vanishes. Completing the s and j sums imposes D*a squared = -C*E and A*a squared = C*B modulo p. Each surviving summand is the phase at the canonical lift times p squared. The sum has at most p minus one terms, the size of the residue field unit group.

**Theorem 1.2 (Vanishing in the mixed sector).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMixedQuotientFourier.coefficient_eq_zero_of_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMixedQuotientFourier.coefficient_eq_zero_of_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If exactly one of A and B reduces to zero, the first residue equation has no unit solution, so the coefficient vanishes.

**Theorem 1.3 (The unit-sector bound and support).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiMixedQuotientFourier.coefficient_unit_sector`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiMixedQuotientFourier.coefficient_unit_sector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If A and B have nonzero reductions, each eligible residue has the same square, so there are at most two of them. The triangle inequality gives the bound 2*p squared. A nonzero coefficient gives a common solution of the two residue equations and hence D/A = -E/B modulo p.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMixedQuotientFourier.coefficient_eq_stationary_sum`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMixedQuotientFourier.coefficient_eq_zero_of_mixed`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiMixedQuotientFourier.coefficient_unit_sector`
