# Common covering points at every good prime

## Abstract

Common covering points at every good prime.

**Theorem 1.1 (Both ordered coverings over the p-adic field).**

Lean statement: `D5/S3/Factorization/Mordell/GoodPrimeCoverings.good_prime_common_tuples`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Mordell/GoodPrimeCoverings.good_prime_common_tuples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural numbers q and r and every prime p not dividing 30qr, let qK be the field unit with value q in Q_p. The theorem supplies the two nonzero common quadruples and their paired equations. Packaging each tuple as FieldKummer.CoveringRep and applying Quotient.mk proves that both FieldKummer.Covering(qr,qK,1) and FieldKummer.Covering(qr,1,qK) are nonempty. No primality or congruence condition on q or r is needed for this local result. In particular the hypotheses q,r distinct primes, q congruent to 1 modulo 24, r congruent to 19 modulo 24, and the three positive Legendre symbols of original79 give this conclusion at every such p.

Each covering point is represented by one nonzero homogeneous quadruple (t,z1,z2,z3); its two equations hold on that same quadruple. The first covering has z2 squared minus q times z1 squared equal to 5qr times t squared and q times z1 squared minus q times z3 squared equal to 15qr times t squared. Dividing the second equation by q gives the source equation z1 squared minus z3 squared equals 15r times t squared; adding gives z2 squared minus q times z3 squared equals 20qr times t squared. The second covering has q times z2 squared minus z1 squared equal to 5qr times t squared and z1 squared minus q times z3 squared equal to 15qr times t squared. The quotient identifies simultaneous multiplication of all four coordinates by one nonzero scalar, as in FieldKummer.CommonRel.

The residue argument uses the existing quadratic character and its vanishing sum. A fractional linear substitution evaluates the character correlation at two distinct shifts as minus one. For the nonsquare q branch, the three coefficient signs are (-1,1,-1) or (1,-1,-1). Expanding the product of the three square-condition weights gives one plus the sum over x of one plus the character of the cubic with shifts 0,-5qr,15qr. Each summand in this last sum is nonnegative, so the product weights cannot all vanish. A single x therefore supplies all three weighted squares simultaneously. This argument does not combine independently chosen conic points.

The Hensel application reuses hensels_lemma and PadicInt.toZMod. The prime restriction makes the three shifts distinct and the coefficients units. If the first residue coordinate vanishes, keep it exactly zero and lift the other two; if only the second vanishes, keep that coordinate zero and lift the other two. Otherwise fix a representative of the third coordinate and lift the first two. Thus the two solved square equations always have nonzero derivative, including root and zero-coordinate cases. The lifted tuple uses t=1 only in this branch. When q is a residue square, a lifted square root supplies explicit t=0 quadruples for both classes. No universal affine normalization is asserted.

This is a repository derivation from finite-field character identities and the pinned Hensel interface. It constructs actual p-adic representatives and then uses the existing common-scaling quotient; it adds no new covering or characteristic-zero framework. LocalKummer base change and the complete FieldKummer fiber bridge remain available without any new membership assumption.

This result covers only primes outside 30qr. Existence at the real place and at 2,3,5,q,r, tangent avoidance, the exceptional q-adic pairing branch, Cassels and quartic-symbol calculations, rank without finite Sha, and all original78 generator, denominator, integrality, quartic and WSS conclusions remain open. Original79 uses the positive mutual residue symbol; no negative mutual symbol from original78 is imported.

## References

- Truth anchor: `D5/S3/Factorization/Mordell/GoodPrimeCoverings.good_prime_common_tuples`
- Dependency: [D5/S3/Factorization/Mordell/FieldKummer](FieldKummer.md)
