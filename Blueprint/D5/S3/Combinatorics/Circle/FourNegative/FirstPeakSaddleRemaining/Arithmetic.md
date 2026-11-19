# Shared arithmetic for high, half and quarter regions

## Abstract

Integer selections and native mask conversion

**Lemma 1.1 (Recover the four unscaled slacks).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/Arithmetic.scaled_to_rectangle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/Arithmetic.scaled_to_rectangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

rectangle lists E+C,A-1-E,H-A+qD,L-C-H in physical argument order t,z,x,y,g,q,r,h,v. scaled_margin avoids division by the auxiliary scale. Positive scale and z+1 together with ps-js=2*scale*(z+1)*v identify each scaled entry with the same positive multiple of its rectangle entry.

**Definition 1.2 (Convert an integer choice to natural masks).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/Arithmetic.native_of_selection`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/Arithmetic.native_of_selection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ArithmeticSelection supplies r,h,v, their capacities and all four rectangle margins with x=4KJt,y=2Kt,g=4KJ,q=2KJt-4KJ. native_of_selection uses K=2^(b-d-1), J=2^(a-b-1), casts nonnegative selections to naturals and sets s=2^(a-d)*(2^(d-1)-1)+r. NativeChoice retains the anchor, grain bound, bit inclusion and rectangle evidence. Each consuming region must supply its own selection; this conversion does not assume or assert arbitrary feasibility.

These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/Arithmetic.native_of_selection`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/Arithmetic.scaled_to_rectangle`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/Descending/Endpoint](../Descending/Endpoint.md)
