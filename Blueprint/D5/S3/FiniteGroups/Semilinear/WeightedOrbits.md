# Weighted finite-field semilinear orbits

## Abstract

The actual weighted semilinear orbit quotient equals the full divisor formula.

**Theorem 1.1 (The actual quotient cardinality).**

Lean statement: `D5/S3/FiniteGroups/Semilinear/WeightedOrbits.orbit_cardinality`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/Semilinear/WeightedOrbits.orbit_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime p, finite field algebra K over ZMod p with cardinality p to the power n, finite coordinate type I in an independent universe, and natural weights w:I to Nat, the group is the actual semidirect product of K units by Gal(K/ZMod p). It acts by ((c,sigma) A)(i)=c to the power -w(i) times sigma(A(i)). Its multiplication is (c,sigma)(b,tau)=(c sigma(b),sigma tau), and the source proves both action laws. Orbits is the native orbit-relation quotient for this action.

Native finite-field Frobenius enumeration identifies the Galois group with the n powers of x maps to x to the power p. The action for sigma=Frobenius to the power j is consequently c to the power -w(i) times A(i) to the power p to the power j. The subgroup degree calculation equals gcd(n,j), including the identity j=0. Neither faithfulness nor freeness is assumed.

The actual fixed subtype is identified with the proved coordinate equations. Native Burnside equates the fixed-point sum with the actual quotient cardinality times n(p to the power n minus one). Substituting the norm-fiber and order sums proves: the orbit cardinality is (1/n) times the sum over d dividing n of [totient(n/d)/(p to the power d minus one)] times the sum over m dividing (p to the power d minus one) of totient(m) times p to the power (d a_m). Here a_m counts all i in I with m dividing w(i). Divisions take place in the rationals, and integrality follows from equality with the finite quotient.

Every partial-zero stratum remains included. Support is preserved because field automorphisms and nonzero scalar powers preserve nonvanishing. On a nonempty support S over the field of size p to the power d, the scalar stabilizers are the common roots of c to the power w(i)=1 for i in S. Cyclicity gives their order as gcd(p to the power d minus one, the weights on S), explaining the support contribution gcd times (p to the power d minus one) to the power (card(S)-1). Empty support contributes one. This is the ordinary support interpretation of the fixed-set mechanism; the Lean endpoint is the complete weighted-action orbit formula.

For I=Fin(n-1) and w(i)=p to the power (i+1) minus p plus one, the same theorem specializes without shortening I for proper divisors d. The known values are M(3,1)=1, M(3,2)=2, M(3,3)=13 and M(3,4)=1692. For the last case the scalar averages at d=1,2,4 are 14,92,6648, with outer multiplicities 2,1,1. The support counts are 1 for empty support; 1,1,2 for the singletons; 23 for each pair; and 1618 for full support.

The same weighted-action proof includes p=2. For odd primes, FiniteJetCoefficients and FiniteJetClassification connect the normalized original jets over every finite field of size p to the power n, n at least one, to these n-1 weighted coordinates. FiniteJetOrbits.quotientEquiv transports the actual original representation quotient, allowing arbitrary original additive relabelings and merely prime-field-linear invertible intertwiners, and FiniteJetOrbits.original_class_cardinality supplies its complete divisor formula in every original field universe. This finite-field bridge does not assert an original-jet classification at p=2 or an arbitrary-field jet classification. No literature priority is claimed. Burnside, Hilbert 90, finite-field Galois theory and cyclic order counts are reused native mathematics. The weighted formal integration supplies weighted fixed-set equivalences, both complete divisor summations and the connection to the actual weighted quotient.

## References

- Truth anchor: `D5/S3/FiniteGroups/Semilinear/WeightedOrbits.orbit_cardinality`
- Dependency: [D5/S3/FiniteGroups/Semilinear/WeightedArithmetic](WeightedArithmetic.md)
