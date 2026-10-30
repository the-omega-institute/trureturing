# Native dyadic transport of a joint ear completion

## Abstract

Native dyadic transport of a joint ear completion

**Definition 1.1 (The same insertion cut).**

Lean statement: `D5/S3/Combinatorics/Circle/RunFirstEarTransport.earWord`

*Formalization.* `D5/S3/Combinatorics/Circle/RunFirstEarTransport.earWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The word inserts the distinct new label d after r old labels. Every old physical occurrence is retained, including different labels with equal values.

**Definition 1.2 (Extend the old-label rotation).**

Lean statement: `D5/S3/Combinatorics/Circle/RunFirstEarTransport.earRelabel`

*Formalization.* `D5/S3/Combinatorics/Circle/RunFirstEarTransport.earRelabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The old cyclic group C_d acts by tau=(finRotate d)^h. Its extension E rotates old labels and fixes the inserted label d; the inverse extends tau inverse. It is a permutation of all d+1 physical labels.

**Theorem 1.3 (Transport any supplied joint completion).**

Lean statement: `D5/S3/Combinatorics/Circle/RunFirstEarTransport.native_dyadic_joint_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/RunFirstEarTransport.native_dyadic_joint_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d>=2, a>=1 and b=2^h*a<2^(d-1). Supply a permutation sigma that is an OriginalOrder at (d,b), and an OriginalOrder at (d+1,2b) obtained by inserting d at cut r<=d. Mapping sigma by tau constructs an OriginalOrder at (d,a) and a new OriginalOrder at (d+1,2a) at exactly the same cut. Every natural old prefix has the identical integer height, and the complete new word is the input word mapped by E. The hypotheses supply the joint witness; the theorem asserts no existence of such a witness.

The native old charge stays at PeriodicShorteningArithmetic. Its exposed digit_data supplies nonnegativity and the exact source equations, while charge_sum is the extracted total-charge proof also consumed by periodic_source_equations. Native alignment gives q_b(i)=q_a(tau(i))+2^j*a for j=tau(i)<h and equality otherwise. At the wrapped seam the old modulus is 2^d-1 while the new modulus is 2^(d+1)-1: the old raw value is 2^d*u and the new raw value is 2^(d+1)*u. Both center to u; replacing the new exponent period by d would be invalid.

Before the cut, the destination height is 2V minus the used a-charge. The input lower bound and charge domination give nonnegativity; the old upper bound gives the destination upper bound. After the cut, total charges rewrite the heights as 2V plus their respective unused suffix charges. Nonnegative unused charge gives the lower bound, and domination now gives the destination upper bound from the input upper bound. These are opposite comparison directions on the two sides of insertion. The proof covers all natural take lengths, including both cut prefixes and saturated takes.

The physical groups C_d and C_(d+1) have different sizes. In the common new-source phase use rho=(finRotate(d+1))^h and C=E composed with rho inverse. The live theorem also gives the pointwise equality between the b-normalized source and the a-normalized source composed with rho, as well as the ear, positive SMALL and odd-predecessor values. It includes C pointwise: identity for h=0; otherwise d maps to 0, each label below h-1 maps to its successor, h-1 maps to d, and every other label is fixed. Thus the common-phase operation cycles the particular SMALL occurrences d,0,...,h-1. Proper periods and nonunits retain separate physical labels. In particular all LARGE labels keep their slots.

The dyadic result keeps arbitrary positive a. An even a need not be the first SMALL in its sign run. For an odd normalized a, the ear at d has value a and its predecessor d-1 has value -(2^(d+1)-1-a)/2, opposite and LARGE; the consecutive cycled labels have positive SMALL values a,2a,...,b. For an original physical source F with selected value s*b at p, normalize the permitted common sign s and read the b-phase at p+1+i and the a-phase at p-h+1+i, modulo d+1. Centered congruence and the doubling recurrence identify these actual source phases; their difference is precisely rho. This keeps physical indices even when values repeat. Consequently an already supplied selected-ear joint witness transports to the odd run start at p-h, without changing the slots of any LARGE labels. This conditional consequence does not produce the initial witness or select a usable run. Existence for an arbitrary source, and hence the full Circle Conjecture 3.1 target of Damasdi, Frankl, Pach and Palvolgyi, remains open. No literature novelty is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/RunFirstEarTransport.earRelabel`
- Truth anchor: `D5/S3/Combinatorics/Circle/RunFirstEarTransport.earWord`
- Truth anchor: `D5/S3/Combinatorics/Circle/RunFirstEarTransport.native_dyadic_joint_transport`
- Dependency: [D5/S3/Combinatorics/Circle/PeriodicShortening](PeriodicShortening.md)
