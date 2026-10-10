# Single-Chain q-Ladder Capacity

## Abstract

A complete p-chain leaves at most q-2 fresh q-ell heights when q is a smaller nonchain prime.

**Theorem 1.1 (The fresh q-ell heights are bounded).**

Lean statement: `D5/S3/Arith/Covering/SingleChainQLadderCapacity.single_chain_q_ladder_height_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/SingleChainQLadderCapacity.single_chain_q_ladder_height_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be an odd distinct whole covering system that is minimal in its number of classes and then in the sum of its moduli. Let p, ell and q be primes with q < p and q different from ell. Suppose every class divisible by p is exactly p times ell to a height below p, and suppose q divides at least one original modulus.

Then at most q-2 heights j below p remain for which no original class has modulus q times ell to the height j. Sum minimality first supplies a pure q class. If at least p-q+2 such heights were missing, the q roots other than the pure-q root could be injected into the remaining p roots. The complete p inventory rules out mixed p-and-q classes; any remaining collision pair is one of the occupied q times ell to a height labels. Prime-root compression would then produce a whole cover with fewer classes, contradicting count minimality.

The conclusion concerns the declared complete p-chain interface. It does not assert a bound for arbitrary prime supports or settle the unrestricted odd covering problem.

## References

- Truth anchor: `D5/S3/Arith/Covering/SingleChainQLadderCapacity.single_chain_q_ladder_height_bound`
- Dependency: [D5/S3/Arith/Congruence/ConditionalComparison/PrimeRootCompression](../Congruence/ConditionalComparison/PrimeRootCompression.md)
- Dependency: [D5/S3/Arith/Covering/PrimeFactorPureClass](PrimeFactorPureClass.md)
- Dependency: [D5/S3/Arith/Covering/SingleChainFreshCompletion](SingleChainFreshCompletion.md)
