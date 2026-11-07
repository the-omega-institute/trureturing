# Actual Quartic Character Moments

## Abstract

The normalized quartic character's actual first Bernoulli value has odd nonzero integer coordinates, obtained from the least-positive representative sums in its ordered kernel cosets. Its analytic L-value at zero is the negative of this same finite sum. The actual CRT kernel has the full coordinate criterion for centered first moments, including conjugation.

Throughout, r is prime, r mod 8 is 5, chi is the unique character with order four and chi(2)=i, K is its actual unit kernel, and m=(r-1)/4. All representatives are ZMod.val. Every unit has representative strictly between zero and r, so these are precisely the source's least-positive representatives. The coordinate theorem and divisibility require r>5. This excludes the singleton kernel at r=5.

**Definition 1.1 (The unit two).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.twoUnit`

*Formalization.* `D5/S3/ArithUnits/MercaQuarticMoments.twoUnit` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The native unit represented by two modulo r. No assumption about its order is made.

**Definition 1.2 (Coset representative sum).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.sumRep`

*Formalization.* `D5/S3/ArithUnits/MercaQuarticMoments.sumRep` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For every native unit c, sumRep r c is the integer sum of val(u) over the finite set of native units u with c inverse times u in K. It is the literal least-positive representative sum s(cK).

**Definition 1.3 (The integral coset coordinate).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.coordinate`

*Formalization.* `D5/S3/ArithUnits/MercaQuarticMoments.coordinate` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The integer expression 2 times the integer quotient s(cK)/r minus m. Divisibility in the following theorem proves the quotient is exact on the r>5 domain; it is not an assumed class number.

**Definition 1.4 (Real coordinate).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.realCoordinate`

*Formalization.* `D5/S3/ArithUnits/MercaQuarticMoments.realCoordinate` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The coordinate k of the identity coset K, in the orientation chi(2)=i.

**Definition 1.5 (Imaginary coordinate).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.imagCoordinate`

*Formalization.* `D5/S3/ArithUnits/MercaQuarticMoments.imagCoordinate` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The coordinate t of the actual coset 2K, in the orientation chi(2)=i.

**Definition 1.6 (The actual first Bernoulli value).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.bernoulli`

*Formalization.* `D5/S3/ArithUnits/MercaQuarticMoments.bernoulli` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

B is the complex sum of val(u) times chi(u) over all native units modulo r, divided by r. Nonunits have character value zero, so this is also the full residue-class sum divided by r.

**Theorem 1.7 (Divisibility, complementation and oddness).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.representative_properties`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaQuarticMoments.representative_properties` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For every prime r>5 with r mod 8 equal to 5, all unit representatives are positive and below r. For every coset cK, r divides s(cK), s(-cK)=r m-s(cK), and its integral coordinate is odd and nonzero. The kernel has m>1 elements. Multiplication by a nonidentity kernel element permutes every coset and fixes its residue-class sum. In the prime field that forces the sum to zero. Negation permutes cK onto -cK and replaces each representative a by r-a. Finally m is odd, so twice an integer minus m is odd.

**Theorem 1.8 (The four quartic values).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.fourth_values`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaQuarticMoments.fourth_values` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

Every complex fourth root of unity is one, i, minus one or minus i. This supplier also gives the pointwise parity used by the actual class-number sign criterion.

**Theorem 1.9 (The actual Bernoulli coordinates and L-value).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.bernoulli_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaQuarticMoments.bernoulli_coordinates` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For every prime r>5 with r mod 8 equal to 5, let k and t be the preceding integer coordinates. Then B=k+i t; k and t are odd and nonzero; k=2s(K)/r-m and t=2s(2K)/r-m in the rationals; B is the literal sum of a chi(a) for a=1,...,r-1 divided by r; and the actual Dirichlet L-function satisfies L(0,chi)=-B. The character fibers are the ordered cosets K, 2K, -K, -2K with values 1, i, -1, -i. Decompose the moment along these fibers and use the complement identities and exact divisibility. For the final analytic equality, apply the existing prime nonprincipal character special-value theorem with its hypotheses discharged.

**Definition 1.10 (The actual lifted kernel).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.liftedKernel`

*Formalization.* `D5/S3/ArithUnits/MercaQuarticMoments.liftedKernel` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

H is the reduction preimage of K in the native units modulo r q.

**Definition 1.11 (The actual CRT identification).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.liftedKernelEquiv`

*Formalization.* `D5/S3/ArithUnits/MercaQuarticMoments.liftedKernelEquiv` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For coprime r and q, the native Chinese remainder equivalence restricts to a multiplicative equivalence from H to K times the full unit group modulo q. Its first coordinate is reduction modulo r.

**Theorem 1.12 (Cyclicity, index and the omitted involution).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.lifted_structure`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaQuarticMoments.lifted_structure` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For distinct primes q and r with r congruent to five modulo eight, H is cyclic exactly when gcd(m,q-1)=1, has index four, and omits minus one. Both CRT factors are cyclic, with orders m and q-1. The finite product cyclicity theorem gives the exact criterion. Surjectivity of reduction preserves the kernel index, and minus one reduces to the already excluded local involution.

**Definition 1.13 (The literal centered sum).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.centered`

*Formalization.* `D5/S3/ArithUnits/MercaQuarticMoments.centered` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The integer identity twice the sum of the least-positive representatives of H equals r q m(q-1). Only H itself is tested.

**Theorem 1.14 (The full prime-lift coordinate criterion).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.centered_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaQuarticMoments.centered_coordinates` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For every prime r>5 congruent to five modulo eight and every distinct prime q, H has order m(q-1), all its native unit representatives are strictly between zero and r q, and its literal sum is centered if and only if chi(q)=1, or k=t and chi(q)=-i, or k=-t and chi(q)=i. The existing coset-fiber lift gives deviation equal to q times s(K)-s(q inverse K). The four values of chi(q) identify the inverse coset. The complement identities give the three branches and k nonzero excludes chi(q)=-1. This finite first-moment identity needs neither q>3 nor q>r; it applies in particular to every admissible odd prime in the MMZ domain. The subsequent class-number and sign bridges remain separate proof obligations.

**Theorem 1.15 (The eligible source generators).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.generator_eligible`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaQuarticMoments.generator_eligible` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For r>5 and distinct odd prime q, every generator of H has representative a with gcd(a-1,r q)=1. Its projections generate both local factors. Both factors have order greater than one, so neither projection is the identity. Reduction shows a-1 is a unit at both primes. Together with lifted_structure this retains exactly the source generator eligibility on gcd(m,q-1)=1.

**Theorem 1.16 (Conjugation and the branch orientation).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.conjugate_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaQuarticMoments.conjugate_coordinates` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The conjugate character has order four, value -i at two, the identical native kernel, value -1 at minus one and value i on -2K. Its actual Bernoulli sum is k+i(-t). Thus the same ordered cosets K,2K,-K,-2K now have values 1,-i,-1,i. The centered branch k=t uses the conjugate q-value i, and k=-t uses -i. This is an explicit simultaneous transformation of character values and imaginary coordinate; the normalized sign formula is not reused unchanged.

**Definition 1.17 (Literal positive interval sums).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.intervalSum`

*Formalization.* `D5/S3/ArithUnits/MercaQuarticMoments.intervalSum` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

intervalSum r chi n is the sum of the actual normalized character at the positive integers from one through n, reduced modulo r.

**Theorem 1.18 (The native representative cutoff).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.intervalSum_eq_zmod`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaQuarticMoments.intervalSum_eq_zmod` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For every cutoff n below r, the literal positive-interval character sum equals the sum over native residues with val at most n; the zero term vanishes. The actual kernel-bin proof consumes this identity.

**Theorem 1.19 (The half and quarter identities).**

Lean statement: `D5/S3/ArithUnits/MercaQuarticMoments.interval_identities`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MercaQuarticMoments.interval_identities` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For every prime r>5 congruent to five modulo eight, let S be the literal half-interval sum and Q the literal quarter-interval sum. Then S=(-2-i)B, S=(1+i)Q and 2Q=(-3+i)B. Consequently 2 Re(Q)=-3k-t and 2 Im(Q)=k-3t. The nonprincipal doubling formula supplies S, and the permutation a maps to 2a below the quarter endpoint and r-2a above it supplies the relation with Q. These are universal literal character sums, independent of the still open signed class-number formula.

## References

- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.bernoulli`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.bernoulli_coordinates`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.centered`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.centered_coordinates`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.conjugate_coordinates`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.coordinate`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.fourth_values`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.generator_eligible`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.imagCoordinate`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.intervalSum`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.intervalSum_eq_zmod`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.interval_identities`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.liftedKernel`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.liftedKernelEquiv`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.lifted_structure`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.realCoordinate`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.representative_properties`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.sumRep`
- Truth anchor: `D5/S3/ArithUnits/MercaQuarticMoments.twoUnit`
- Dependency: [D5/S3/Analytic/Zeta/PrimeQuadraticLValues](../Analytic/Zeta/PrimeQuadraticLValues.md)
- Dependency: [D5/S3/ArithUnits/MercaCosetFiberLift](MercaCosetFiberLift.md)
- Dependency: [D5/S3/ArithUnits/MercaPrimeCharacterMoment](MercaPrimeCharacterMoment.md)
- Dependency: [D5/S3/ArithUnits/MercaQuarticCharacter](MercaQuarticCharacter.md)
