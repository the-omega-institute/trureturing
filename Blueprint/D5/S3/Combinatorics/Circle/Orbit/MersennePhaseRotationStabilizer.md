# The full physical rotational stabilizer

## Abstract

The full physical integer-zero family is preserved by forward rotation through h labels exactly when d divides h, except at d=4 where exactly the even exponents preserve it.

Let d and h be natural numbers, assume d at least three and 19 not dividing m=2^(d+1)-3, and put g=2^d-1, k=3d, N=2^k-1 and t=g*m. All subsets A of the original Fin(k) labels are in scope. Rotate A by its forward image under finRotate(k)^h and use the literal centered integer source SourceWidth.actualSource(k,t). Equal-valued labels stay distinct; neither the seed nor the source values are required to be units.

**Theorem 1.1 (Exact preservation for every exponent).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersennePhaseRotationStabilizer.actual_zero_family_rotation_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersennePhaseRotationStabilizer.actual_zero_family_rotation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

MersennePhaseNoncyclicFamily.actual_zero_iff_phase_pair classifies every physical zero subset uniquely as phaseLift(d,B), where j belongs to B exactly when the complete triple j,j+d,j+2d is selected, and a=d-3 belongs to B exactly when b=d-1 does. Induction proves that finRotate(n)^h sends i to (i+h) modulo n for every h, including zero and h at least k. Reduction modulo d commutes with that physical rotation. Taking the image of a phaseLift is therefore exactly the phaseLift of the rotated phase selection; the first-representative read map makes phaseLift injective.

For a singleton phase selection B={j}, its physical triple is zero exactly when j is outside {a,b}. Preservation of the full physical zero family transports these singleton tests, forcing the induced phase permutation to preserve the two-point support {a,b}. If a is fixed then e=h modulo d is zero. Otherwise a goes to b, so e=2, and injectivity forces b to go to a. The two explicit possible modular wraps then force d=4. This is a necessity argument using the actual zero family, with no support-preservation assumption.

Conversely e=0 fixes the two distinguished phases, while d=4 and e=2 swaps them. Both cases preserve the paired-selection equivalence for every phase subset. The exact physical classification and phaseLift image identity transport this equivalence in both directions for arbitrary physical A. Finally e=0 or (d=4 and e=2) is precisely divisibility of h by d, or by 2 in the exceptional case. No bounded-exponent or modular-zero replacement is used.

Application to the finite cyclic rotation group: among exponents from 0 through 3d-1 the stabilizer is {0,d,2d}, of order three, when d differs from four. At d=4 it is {0,2,4,6,8,10}, of order six. These group-order statements are consequences of the checked iff and the elementary enumeration of multiples; they are exposition here, not separately retained named Lean corollaries.

For comparison take the minus seed t0=g at the same k=3d. The existing MersenneDifferenceZeroSubsets.actual_zero_iff_rotation identifies its physical zero subsets with the subsets invariant under rotation by d; arbitrary rotations commute with that rotation and preserve this condition in both directions. Equivalently these are all complete phase unions, without a paired-selection restriction. Its family stabilizer is thus the full cyclic rotation group, of order 3d, and its physical zero-family count is 2^d by the existing minus count. The phase-family count is 2^(d-1). The consumed gcd identity gives gcd(t,N)=g under the stated exclusion of 19, while the standard minus gcd identity gives gcd(t0,N)=g; equal gcd does not determine these family stabilizers. For any admissible d=18r+3, d is odd and the phase-family stabilizer has order three. This comparison is conditional on the cited classification, minus and arithmetic dependencies; it introduces no additional Lean theorem.

The exclusion of 19 and d at least three are retained assumptions. No conclusion is asserted at excluded parameters, no full Circle solution or literature novelty is claimed, and this delivery supplies no independent-review or official-acceptance verdict. The new full-telescope Reg has compiled source equivalence, actual law, variation, separate role sensitivity and dependence proofs, but the native binding is declared_unresolved at IE-C050, reason unclassified_form, rule source.statement_reconstruction. Its selector/representation compatibility remains unverified; no specific reconstruction mismatch or judge defect is established. The same two-readout reconstruction boundary is tracked by existing issue https://github.com/the-omega-institute/trureturing/issues/18956, which concerns a different theorem. This exact attempt is recorded in the delivery evidence; no issue mutation is made. The inherited minus/TwoBit Nat.gcd count audits remain unfinished under https://github.com/the-omega-institute/trureturing/issues/11434; their source and evidence are preserved.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersennePhaseRotationStabilizer.actual_zero_family_rotation_iff`
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersennePhaseNoncyclicFamily](MersennePhaseNoncyclicFamily.md)
