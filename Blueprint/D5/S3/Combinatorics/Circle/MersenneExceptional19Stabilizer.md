# The exceptional19 full physical rotational stabilizer

## Abstract

For every natural r, the exceptional19 physical integer-zero family has trivial cyclic rotational stabilizer: rotation by any natural a preserves every zero subset exactly when 3(18r+12) divides a.

Set d=18r+12, B=2^d, g=B-1, H=B^2+B+1 and N=2^(3d)-1=gH. The original natural seed is t=(2^d-1)(2^(d+1)-3). Every subset of the original Fin(3d) labels is quantified, and its sum is the literal integer sum of SourceWidth.actualSource(3d,t). Rotation takes its image under finRotate(3d)^a. The statement includes r=0, a=0, and all a at least 3d; it imposes no unit, nonemptiness, distinct-value or profile premise.

**Theorem 1.1 (Exact preservation for every r and every exponent).**

Lean statement: `D5/S3/Combinatorics/Circle/MersenneExceptional19Stabilizer.actual_zero_family_rotation_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/MersenneExceptional19Stabilizer.actual_zero_family_rotation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first arithmetic step proves B modulo 19 equals 11 for every r by reducing powers modulo the period 18. Thus Q=H/19 is an integer. The already proved binary-mask injection, bounds and surjectivity realize Q as an actual physical subset. Its rotations are images of that subset; labels that happen to have equal source values remain distinct. Congruence and strict mask bounds identify the first d rotated masks with 2^j Q, and exact base-B digit uniqueness identifies their three physical blocks.

The existing centered_scaled uniqueness argument identifies all actual physical weights. At local index j they are g times (2B-3)2^j-H[ j=d-1 ], -(5B+2)2^j+H([ j=d-3 ]+[ j=d-2 ]+2[ j=d-1 ]), and (3B+5)2^j-H([ j=d-2 ]+2[ j=d-1 ]). The doubled centered bounds are checked in the interior and at each of the last three indices. Summing over the three literal label slices gives an identity for every physical subset, using its actual top bits and exact integer floor divisions.

For 0<=j<d put n=2^j, s=n modulo 19 and z=12s modulo 19. The rotated Q blocks are L=(zB+n)/19, M=(sB+n-z)/19 and U=(n-s)/19. The proof establishes divisibility, exact block equations, 0<=L,M<B and 0<=8U<B. Rotation through d cyclically permutes (L,M,U). Interior floor identities follow from their strict remainder bounds; the three endpoint floors are established separately, including r=0. Exhausting only the 18 ordinary residues gives the full profile P0^r T0 P1^r T1 P2^r T2. This finite residue calculation establishes a formula for unbounded r; it is not a finite-r control or an assumed profile.

In residue order 0 through 17, P0=(0,0,0,0,-1,0,0,0,0,0,0,0,0,1,0,0,0,0), P1=(0,0,0,0,-1,0,0,-1,0,-1,-1,-1,-1,0,-1,-1,0,-1), and P2=(0,0,0,1,1,1,1,0,1,1,1,1,0,0,0,0,1,0). Each tail has length twelve: T0=(0,0,0,0,-1,0,0,0,0,0,0,-1), T1=(0,0,0,0,-1,0,0,-1,0,0,-1,-1), and T2=(0,0,0,1,1,1,1,0,1,1,0,0). Thus r=0 consists of just these three tails. Writing floor for integer division, the full arbitrary-mask formula is S(A)=g*((2B-3)L-(5B+2)M+(3B+5)U+H*(-floor(2L/B)+floor(8M/B)-floor(4M/B)-floor(4U/B))). For rotated Q blocks the interior floors are floor(ell*L/B)=floor(ell*z/19) and floor(ell*M/B)=floor(ell*s/19), for ell=2,4,8. The L corrections are respectively [j=d-1], [j=d-2]+[j=d-1], and [j=d-3]+[j=d-2]+[j=d-1]; the M floors have no correction. The U floors are zero. These are exact floor identities, including the three endpoints, and yield the displayed complete profile.

The literal sum of every rotated Q is N times that proved profile. The zero predicate includes all endpoint corrections. A maximal run of exactly three consecutive zero positions, with both adjacent positions nonzero, occurs uniquely at 2d modulo 3d. This cyclic run calculation is proved for every r. If rotation by a preserves the full physical zero family, testing it on every rotated Q transports the entire zero predicate and therefore that unique marker. It forces (2d+a) modulo 3d to equal 2d, hence 3d divides a. Conversely the existing unrestricted power-of-finRotate value law proves period 3d, so every multiple of 3d acts identically on every physical subset. No restriction to bounded shifts is used.

Consequently, in the cyclic rotation group on the original 3d labels, only the identity preserves this exceptional family's integer-zero subsets. For comparison, the sealed MersennePhaseRotationStabilizer.actual_zero_family_rotation_iff applies when d>=3 and 19 does not divide 2^(d+1)-3: its family stabilizer has order three, or order six at d=4. Those comparison statements are conditional on the cited exact nonexceptional prerequisite and its hypotheses; its hypothesis fails for d=18r+12. This exposition introduces no additional public bind-only corollary or zero-family count.

The ordinary all-r proof supplied through GPT Pro informed this Codex implementation. Its mathematical input was not kernel evidence. This delivery claims no literature novelty, independent review, official acceptance, or full Circle solution. The guarded full Lean build succeeds, and the coherent native report records only Classical.choice, Quot.sound and propext for the exact theorem. The faithful full-telescope Reg also compiles, and its two source readout paths were checked against the actual native type. Its native assessment remains declared_unresolved: IE-C050 ClosedTruthReadout, reason unclassified_form, rule source.statement_reconstruction. This missing reconstruction evidence is preserved without a waiver or manual validation. The original three RadixFourDigitBalance bindings remain declared_validated; the nonexceptional rotation binding and inherited Nat.gcd count bindings keep their existing unresolved states.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/MersenneExceptional19Stabilizer.actual_zero_family_rotation_iff`
- Dependency: [D5/S3/Combinatorics/Circle/MersennePhaseRotationStabilizer](MersennePhaseRotationStabilizer.md)
- Dependency: [D5/S3/Combinatorics/Circle/MersennePhaseThreeTrace](MersennePhaseThreeTrace.md)
- Dependency: [D5/S3/Combinatorics/Circle/TwoBitZeroSubsets](TwoBitZeroSubsets.md)
- Dependency: [D5/S3/Combinatorics/Circle/ZeroSumSubsets](ZeroSumSubsets.md)
