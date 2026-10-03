# Prime-Power Traces and Dedekind's Different

## Abstract

A prime-power quotient filtration computes the residue trace, and a Chinese remainder lift detects the tame different exponent.

**Theorem 1.1 (Trace on a prime-power quotient).**

$$\forall n, z, \operatorname{quotientPowerTrace}\left(n, z\right) = n \operatorname{residueTrace}\left(z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Dedekind/TameDifferent.prime_power_quotient_trace` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *Prime-power quotient traces and Dedekind's different theorem*. URL: <https://github.com/TauCetiProject/TauCeti/tree/33c2099c678ea391f7ea3e0ddaf945a76a625e5d>.

*Commentary.*

Let A and B be commutative rings, with B a module-finite A-algebra and a Dedekind domain. Let p and P be maximal ideals in A and B, with P nonzero. For any natural n, assume both B/P to the n and B/P carry A/p-algebra structures compatible with the A actions. For every z in B, the trace of its image in B/P to the n is n times its trace in B/P. The zero exponent is included.

Multiplication by an element in P to the n but outside P to the n plus one gives the first map in an exact quotient sequence. After splitting that sequence over the residue field, the multiplication operator has two diagonal blocks and a zero-trace off-diagonal block. Induction gives the formula.

**Theorem 1.2 (The next prime power detects wild ramification).**

$$P^{e} divides \operatorname{different}\left(B, A\right) \iff \operatorname{ResidueInseparable}\left(P\right) \lor \operatorname{residueCast}\left(e\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Dedekind/TameDifferent.prime_power_divides_different_iff` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *Prime-power quotient traces and Dedekind's different theorem*. URL: <https://github.com/TauCetiProject/TauCeti/tree/33c2099c678ea391f7ea3e0ddaf945a76a625e5d>.

*Commentary.*

Let A and B be Dedekind domains with B finite and torsion free over A, and with separable fraction-field extension. Let p be a nonzero maximal ideal of A and P a maximal ideal of B over p. If pB equals P to the e times a coprime ideal Q, then P to the e divides the different exactly when the residue extension is inseparable or e vanishes in A/p.

The inverse fractional ideal converts different divisibility into integral trace membership. The Chinese remainder decomposition turns this trace into e times the residue trace. In the tame case a residue with nonzero trace lifts into Q and excludes divisibility by P to the e.

Together with the pinned universal lower bound, the criterion computes the different exponent as e minus one at tame primes. Golden cubic field discriminants also require their actual prime support, ramification indices, completion maps and the global different-to-discriminant calculation.

## References

- Truth anchor: `D5/S3/Factorization/Dedekind/TameDifferent.prime_power_divides_different_iff`
- Truth anchor: `D5/S3/Factorization/Dedekind/TameDifferent.prime_power_quotient_trace`
