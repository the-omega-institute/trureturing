# Cubic Gauss Sums, Frobenius, and Primary Reciprocity

## Abstract

Gauss sums and two Frobenius comparisons give cubic reciprocity at distinct rational prime residue cardinalities.

Write E = Z[omega], with omega the standard primitive cube root of unity in the Eisenstein order. For a maximal ideal P with finite residue field of cardinality congruent to 1 modulo 3 and with 3 not in P, chi_P is the existing Euler cubic residue character on E/P, extended by zero at zero. Its nonzero values are the unique elements of {1, omega, omega^2} reducing to x^((card(E/P)-1)/3). An expression chi_P(a) for a in E means evaluation at a mod P. A primary generator pi means exactly (pi) = P and 3 divides pi-1.

For the arithmetic comparison and reciprocity endpoints below, p and q are distinct rational primes, both congruent to 1 modulo 3. The maximal ideals P and Q have residue cardinalities exactly p and q. Thus their residue characteristics are p and q. Prime cardinality is a hypothesis of these endpoints; it is not replaced by a prime-power cardinality. The companion CubicJacobiNormalization supplies J(chi_P,chi_P) = -pi and Norm(pi) = p from the stated generator and primary assumptions, rather than taking either identity as a premise.

**Theorem 1.1 (The finite-sum convention fixes the inverse character value).**

$$\forall F, K, \operatorname{field}\left(F\right), \operatorname{finite}\left(F\right), \operatorname{field}\left(K\right), \forall chi: \operatorname{MulChar}\left(F, K\right), \operatorname{orderOf}\left(chi\right)=3, \forall psi: \operatorname{AddChar}\left(F, K\right), \operatorname{primitive}\left(psi\right), \forall q: Nat, \operatorname{prime}\left(q\right), \operatorname{CharP}\left(K, q\right), \operatorname{mod}\left(q, 3\right)=1, \operatorname{isUnit}\left(\operatorname{cast}\left(q, F\right)\right), \operatorname{neq}\left(\operatorname{cast}\left(\operatorname{card}\left(F\right), K\right), 0\right) \implies \operatorname{inv}\left(\operatorname{chi}\left(\operatorname{cast}\left(q, F\right)\right)\right)=\operatorname{pow}\left(\operatorname{mul}\left(\operatorname{cast}\left(\operatorname{card}\left(F\right), K\right), \operatorname{jacobiSum}\left(chi, chi\right)\right), \operatorname{natDiv}\left(q-1, 3\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius.cubic_gauss_euler_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here F is a finite field, K is a field of prime characteristic q, chi : MulChar F K has exact order three, and psi : AddChar F K is primitive. In addition to q congruent to 1 modulo 3, the cast of q in F must be a unit and the cast of card(F) in K must be nonzero. These are the actual parameters of this reusable finite-sum statement. With Mathlib's convention G = sum_x chi(x) psi(x), gaussSum_frob, AddChar.pow_mulShift, and gaussSum_mulShift_eq give G^q = chi(q)^(-1) G. The character is not replaced by its inverse, and the additive character is not replaced by psi^(-1). The exact cubic Gauss identity is G^3 = card(F) J(chi,chi); its cardinality factor is not inverted. Primitivity, nontriviality of chi, and the nonzero cardinality cast give G nonzero. Cancelling G and using q-1 = 3((q-1)/3) yields the displayed inverse-character comparison. This lemma alone is not a prime-power reciprocity statement.

**Theorem 1.2 (Only the three cubic roots are transported injectively).**

$$\forall K, \operatorname{commRing}\left(K\right), \operatorname{isDomain}\left(K\right), \forall f: \operatorname{ringHom}\left(E, K\right), \operatorname{neq}\left(\operatorname{f}\left(3\right), 0\right), \forall z, zPrime: E, \operatorname{IsCubicRoot}\left(z\right), \operatorname{IsCubicRoot}\left(zPrime\right), \operatorname{f}\left(z\right)=\operatorname{f}\left(zPrime\right) \implies z=zPrime$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius.cubic_roots_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

IsCubicRoot(z) means the literal disjunction z = 1 or z = omega or z = omega^2. For a ring homomorphism f : E -> K into a commutative domain, the hypothesis f(3) nonzero keeps these three images distinct. The proof uses omega^2+omega+1 = 0 and (1-omega)(1-omega^2) = 3. No global injectivity of f is asserted. In the arithmetic application, f factors through E/Q and has a kernel; only its restriction to these three roots is used to lift equalities. The field inclusion E/Q -> K is a different map and is injective.

**Theorem 1.3 (Primary Jacobi normalization determines the Gauss scalar).**

$$\forall P: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \forall p, q: Nat, \operatorname{prime}\left(p\right), \operatorname{prime}\left(q\right), \operatorname{mod}\left(p, 3\right)=1, \operatorname{mod}\left(q, 3\right)=1, \operatorname{neq}\left(p, q\right), \operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right)=p, \forall pi: E, \operatorname{spanSingleton}\left(pi\right)=P, \operatorname{divides}\left(\operatorname{cast}\left(3, E\right), pi-1\right), \forall K, \operatorname{field}\left(K\right), \operatorname{CharP}\left(K, q\right), \forall f: \operatorname{ringHom}\left(E, K\right), \operatorname{neq}\left(\operatorname{f}\left(3\right), 0\right), \forall psi: \operatorname{AddChar}\left(\operatorname{quotient}\left(E, P\right), K\right), \operatorname{primitive}\left(psi\right) \implies \operatorname{inv}\left(\operatorname{f}\left(\operatorname{chi}\left(P, \operatorname{modIdeal}\left(\operatorname{cast}\left(q, E\right), P\right)\right)\right)\right)=\operatorname{pow}\left(\operatorname{f}\left(\operatorname{mul}\left(-\operatorname{cast}\left(p, E\right), pi\right)\right), \operatorname{natDiv}\left(q-1, 3\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius.cubic_gauss_primary_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar statement takes P maximal with finite residue field of cardinality p, distinct rational primes p and q both congruent to 1 modulo 3, and a specified primary generator pi of P. It also takes a field K of characteristic q, a ring homomorphism f : E -> K with f(3) nonzero, and a primitive additive character psi : AddChar (E/P) K. These are explicit parameters at this intermediate endpoint. Restricted cubic-root transport preserves the exact order three of the transported P-character. Distinctness p != q gives the nonzero casts required in the finite-sum lemma. Reuse of the companion Jacobi normalization replaces J_P by -pi, so the cube scalar becomes -p pi. Consequently the left side is f(chi_P(q))^(-1), with the inverse retained. No Gauss cube identity, Frobenius eigenvalue, or Jacobi value is added as an assumption.

**Theorem 1.4 (The asymmetric comparison for the actual residue characters).**

$$\forall P, Q: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{maximal}\left(Q\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, Q\right)\right), \forall p, q: Nat, \operatorname{prime}\left(p\right), \operatorname{prime}\left(q\right), \operatorname{mod}\left(p, 3\right)=1, \operatorname{mod}\left(q, 3\right)=1, \operatorname{neq}\left(p, q\right), \operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right)=p, \operatorname{card}\left(\operatorname{quotient}\left(E, Q\right)\right)=q, \forall pi: E, \operatorname{spanSingleton}\left(pi\right)=P, \operatorname{divides}\left(\operatorname{cast}\left(3, E\right), pi-1\right) \implies \operatorname{chi}\left(P, \operatorname{modIdeal}\left(\operatorname{cast}\left(q, E\right), P\right)\right)=\operatorname{mul}\left(\operatorname{chi}\left(Q, \operatorname{modIdeal}\left(pi, Q\right)\right), \operatorname{pow}\left(\operatorname{chi}\left(Q, \operatorname{modIdeal}\left(\operatorname{star}\left(pi\right), Q\right)\right), 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius.cubic_residue_prime_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This arithmetic endpoint assumes P and Q maximal, both quotients finite, card(E/P) = p, card(E/Q) = q, p and q rational primes congruent to 1 modulo 3, p != q, and pi a primary generator of P. It has no supplied extension field, map f, or additive character as an extra hypothesis. The proof constructs a primitive additive character of E/P in a cyclotomic extension of E/Q. Its characteristic is q. The reduction f : E -> K factors through Q, and f(3) is nonzero.

Normalization derives Norm(pi) = p, hence p = pi star(pi). Since p is nonzero modulo Q, both pi and star(pi) are nonzero there; q is likewise nonzero modulo P. Put a = chi_P(q), b = chi_Q(pi), c = chi_Q(star(pi)), and d = chi_Q(-p pi). Euler reduction at Q turns the scalar identity into f(a)^(-1) = f(d). The cubic-root restriction lifts the resulting product to a d = 1 in E. Multiplicativity, p = pi star(pi), and chi_Q(-1) = 1 give d = b^2 c. The cubic-root relations then give a = b c^2, exactly the displayed direction. The inverse in the Gauss comparison is therefore essential to the final orientation.

**Theorem 1.5 (Two derived Gauss comparisons give primary cubic reciprocity).**

$$\forall P, Q: \operatorname{Ideal}\left(E\right), \operatorname{maximal}\left(P\right), \operatorname{maximal}\left(Q\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, P\right)\right), \operatorname{finite}\left(\operatorname{quotient}\left(E, Q\right)\right), \forall p, q: Nat, \operatorname{prime}\left(p\right), \operatorname{prime}\left(q\right), \operatorname{mod}\left(p, 3\right)=1, \operatorname{mod}\left(q, 3\right)=1, \operatorname{neq}\left(p, q\right), \operatorname{card}\left(\operatorname{quotient}\left(E, P\right)\right)=p, \operatorname{card}\left(\operatorname{quotient}\left(E, Q\right)\right)=q, \forall pi: E, \operatorname{spanSingleton}\left(pi\right)=P, \operatorname{divides}\left(\operatorname{cast}\left(3, E\right), pi-1\right), \forall rho: E, \operatorname{spanSingleton}\left(rho\right)=Q, \operatorname{divides}\left(\operatorname{cast}\left(3, E\right), rho-1\right) \implies \operatorname{chi}\left(Q, \operatorname{modIdeal}\left(pi, Q\right)\right)=\operatorname{chi}\left(P, \operatorname{modIdeal}\left(rho, P\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius.cubic_reciprocity_primary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the final endpoint, pi and rho are specified elements of E satisfying (pi) = P, (rho) = Q, 3 divides pi-1, and 3 divides rho-1, in addition to all the prime-cardinality and distinctness assumptions above. Norm(pi) = p and Norm(rho) = q are derived from CubicJacobiNormalization. No reciprocity identity, Jacobi value, norm identity, or choice between conjugate ideals is assumed by the final statement.

Set A = chi_Q(pi), B = chi_Q(star(pi)), C = chi_P(rho), and D = chi_P(star(rho)). The first arithmetic comparison and q = rho star(rho) give C D = A B^2. Applying the same comparison with P,p,pi and Q,q,rho exchanged gives A B = C D^2. These two comparisons are proved before invoking cubic_reciprocity_algebra; they are not arithmetic premises. The algebra helper needs only A^3 = B^3 = 1 and those two comparisons. It obtains B D = 1 and then A = C, without a global injectivity premise for reduction.

This is classical cubic reciprocity for distinct rational prime residue cardinalities. The convention and classical context are recorded in Dunn and Radziwill, arXiv:2109.07463v3, equations (1.4)-(1.5). The proof combines the Euler selector, the companion Jacobi normalization, and Mathlib's exact Gauss, Jacobi, and additive-character identities.

Scope still outside this arithmetic endpoint: general prime-power residue cardinalities, including the cardinality-four case covered by the companion normalization; equal residue characteristics; the two conjugate primes over one rational prime; ramified primes at three; and a reciprocity statement for arbitrary composite ideals. The present final theorem does not assert those extensions. The finite-sum lemmas and the normalization lemma retain their own separately stated domains.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius.cubic_gauss_euler_comparison`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius.cubic_gauss_primary_scalar`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius.cubic_reciprocity_primary`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius.cubic_residue_prime_comparison`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/CubicGaussFrobenius.cubic_roots_injective`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization](CubicJacobiNormalization.md)
