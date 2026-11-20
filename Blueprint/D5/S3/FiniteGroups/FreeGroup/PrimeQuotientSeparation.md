# Free groups are residually p for every prime

## Abstract

Every nonidentity free-group element survives in a finite p-group quotient for every prime p.

**Theorem 1.1 (A normal subgroup separating a prescribed word).**

$$\forall u \in UniverseLevel,\; \forall X \in Type\left(u\right),\; \forall p \in Nat,\; \forall instPrime \in \operatorname{Fact}\left(Nat.Prime\left(p\right)\right),\; \forall w \in \operatorname{FreeGroup}\left(X\right),\; \forall hw \in \left(\neg w = 1\right),\; \exists N \in \operatorname{Subgroup}\left(\operatorname{FreeGroup}\left(X\right)\right),\; \exists instNormal \in Subgroup.Normal\left(N\right),\; Subgroup.FiniteIndex\left(N\right) \land \left(\operatorname{IsPGroup}\left(p, HasQuotient.Quotient\left(\operatorname{FreeGroup}\left(X\right), N\right)\right) \land \left(\neg Membership.mem\left(N, w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FreeGroup/PrimeQuotientSeparation.exists_normal_is_p_group_quotient_not_mem` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *Free groups are residually p*. URL: <https://github.com/TauCetiProject/TauCeti/blob/d91980bdc255e6e50506be147ad9bcb88eb9fcc0/TauCeti/GroupTheory/FreeGroup/ResiduallyP.lean>.

*Commentary.*

For every universe u, alphabet X in Type u, prime natural number p, and element w of FreeGroup X with w distinct from the identity, there exists a normal subgroup N of finite index excluding w such that FreeGroup X modulo N is a p-group. The alphabet may be infinite and need not be countable or have decidable equality. An empty alphabet is included: its free group has no nonidentity element, so the hypothesis on w excludes that case.

Express w as a normal syllable product x_1 raised to e_1 through x_k raised to e_k, where each integer exponent is nonzero and adjacent letters differ. Give syllable i a run of length p raised to v_p(e_i), and let D be the sum of these lengths. For each x in the entire alphabet, its shift matrix has entry one at (a,b) precisely when b=a+1 and the letter at column b is x. Sending every generator x to one plus this shift gives a homomorphism into the existing upper unitriangular subgroup of the special linear group over ZMod p, in dimension n=D+1.

The upper-entry coordinates have q=n(n-1)/2 free coordinates, so this finite group has cardinality p raised to q. Its elements therefore have period dividing p raised to K, where K=q+n. Reduce every signed exponent modulo p raised to K and take the nonnegative natural representative. This includes negative exponents and exponents divisible by p.

A power of one plus a shift has binomial entries along constant letter intervals. The first-row invariant says that after a prefix of total weight L the row vanishes beyond column L and is nonzero at L. Adjacent distinct letters make each run maximal at both ends. In the next run the sole possible contribution to the terminal entry comes from column L. The inequality p raised to v_p(e) at most D implies v_p(e)<K; Lucas congruences then show that the relevant binomial coefficient is nonzero modulo p. The invariant reaches column D. Since D is positive, this nonzero (0,D) entry distinguishes the image of w from the identity.

Take N to be the kernel of this homomorphism. Its finite image gives finite index, and the quotient embeds in the finite p-group through the kernel lift. Surjectivity onto the full unitriangular group is unnecessary. The separating quotient depends on the chosen word and prime. There is no fixed observation budget, executable inverse, or resource guarantee.

The syllable normalization, valuation-binomial argument, and first-row induction are adapted from the Tau Ceti contributors' immutable source identified in the Library note. The carrier and period use the existing upper-entry chart and cardinality theorems. The source attests the formal mathematical statement; Magnus and Iwasawa are cited there, but their primary papers are not used as independently read sources here.

## References

- Truth anchor: `D5/S3/FiniteGroups/FreeGroup/PrimeQuotientSeparation.exists_normal_is_p_group_quotient_not_mem`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard](../NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.md)
