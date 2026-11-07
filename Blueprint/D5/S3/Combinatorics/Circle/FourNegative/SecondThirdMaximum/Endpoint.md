# Every natural 2<=a<d<b=c

## Abstract

Second and third maxima: the full original face

**Theorem 1.1 (One original sigma, one literal ear, all repetitions).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondThirdMaximum/Endpoint.actualSource_second_third_maximum_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondThirdMaximum/Endpoint.actualSource_second_third_maximum_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source telescope is exactly (a b c d : Nat) (ha : 2<=a) (had : a<d) (hdb : d<b) (hbc : b=c). It keeps k=a+b+c+d and seed A=1+2^a+2^(a+b)+2^(a+b+c). The theorem states the existence of one sigma : List (Fin k) and one natural j<=k, OriginalOrder k A sigma, and OriginalOrder (k+1) (2A) (earWord k sigma j). Internally the bank construction uses the literal cut zero and PacketNormalForm's original-source bridge. There is no additional domain restriction, selector premise, or finite parameter bound.

The endpoint states all natural m,n repeat/flatten/take windows explicitly: old sums lie in [0,modulus(k)/2] and enlarged sums lie in [0,modulus(k)]. It also states both complete repeated sums equal zero, separately, for every natural m. The existing zero_period_transport proof inducts over m using the complete zero total, so zero repetitions, zero takes and takes beyond the flattened word are included. The identity modulus(k+1)/2=modulus(k) provides the enlarged bound. The single-period zero totals are part of the two OriginalOrder predicates and descend from the actual-source totals, not from a weakened window predicate.

The source-bound Reg mirror uses the enrolled DependentFamily.realize template with all four natural parameters and an infinite natural seed state. Its two finite roles read the actual old and enlarged OriginalOrder predicates. Law contains the entire endpoint telescope and all repeated windows and totals. The bridge is intended as definitional equivalence. Variation rejects the whole readout family; each coordinate intervention deletes one role while fixing the other and all anchors. Actual observational dependence uses an in-domain parameter point and distinct seeds, and is not a claim that every fiber varies. The sourceSelection retains coordinates 0,1,2,3 and both actual readout locations. continuation.unknown records only an unclassified residual, not undecidability or inexhaustibility.

The construction and the explicit grid lemma are attributed by SHA256 in the Arithmetic narrative. The argument concerns this face of labeled centered modular words and does not establish the unrestricted Circle/J/C3.1 four-negative goal, which remains open. No claim of literature novelty or official acceptance is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondThirdMaximum/Endpoint.actualSource_second_third_maximum_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakMiddleGap/Endpoint](../SecondPeakMiddleGap/Endpoint.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondThirdMaximum/Physical](Physical.md)
