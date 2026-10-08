# Single-Chain Cofactor Bound

## Abstract

A complete saturated prime chain forces its cofactor prime below the chain prime.

**Theorem 1.1 (The cofactor prime is smaller than the chain prime).**

Lean statement: `D5/S3/Arith/Covering/SingleChainCofactorBound.single_chain_cofactor_lt_prime`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/SingleChainCofactorBound.single_chain_cofactor_lt_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be an actual whole covering system with pairwise distinct odd moduli greater than one, minimal in its number of classes and then in the sum of its moduli. Let p and ell be distinct primes. Assume that every original modulus divisible by p is one of the p ell^j classes for j in Fin p, and that their residues modulo p are injective.

Then ell is strictly smaller than p. The proof takes the p class at height zero and one of its private points. This point avoids every p-free original class. The complete-chain residual theorem aligns it with every ell^j coordinate. Sum minimality supplies an actual pure ell class from the ell-divisible chain member.

If ell were larger than p, choose an injective assignment from the p roots other than the guard root to ell roots while avoiding the private-point root and the pure-ell donor root. The two root exclusions leave enough ell roots. Chain mixed classes are excluded by the common residual alignment. Any possible collision between an ell u class and a p u class forces u to be an ell-chain power; coprimality then forces u=1, so only the pure-ell donor collision remains. The existing prime-root compression therefore constructs a whole odd distinct cover with fewer classes, contrary to count minimality.

This is a conditional structural result for the declared complete chain interface. It does not settle the unrestricted odd covering problem and does not assert that arbitrary prime supports admit such a chain.

## References

- Truth anchor: `D5/S3/Arith/Covering/SingleChainCofactorBound.single_chain_cofactor_lt_prime`
- Dependency: [D5/S3/Arith/Congruence/ConditionalComparison/PrimeRootCompression](../Congruence/ConditionalComparison/PrimeRootCompression.md)
- Dependency: [D5/S3/Arith/Covering/ConcentratedPrimeSingleton](ConcentratedPrimeSingleton.md)
- Dependency: [D5/S3/Arith/Covering/PrimeFactorPureClass](PrimeFactorPureClass.md)
- Dependency: [D5/S3/Arith/Covering/SingleChainFreshCompletion](SingleChainFreshCompletion.md)
