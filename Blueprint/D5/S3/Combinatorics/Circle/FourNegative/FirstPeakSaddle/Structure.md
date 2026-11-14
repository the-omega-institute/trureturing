# Interface between arithmetic and physical reconstruction

## Abstract

Natural masks and paired physical seams

**Definition 1.1 (Twelve paired gate margins).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Structure.gate`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Structure.gate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The private gate takes integer arguments in the order t,z,x,y,s,r,h,v. Write D=y(z+1)+1, A=xD+1, B=xt(y+1)+t+1, L=xzt+zt+z+1, M=tyz+D and Bn=2B-1, Ln=2L-z-1, Mn=2M-D. Its Fin12 entries are E1,A-1-E1,F1,A-1-F1,E2,L-1-E2,F2,Ln-1-F2,E3,B-1-E3,F3,Bn-1-F3. Each pair bounds a doubled physical seam and its successor slack.

**Definition 1.2 (Native capacities and bit inclusion).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Structure.JointChoice`

*Formalization.* `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Structure.JointChoice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

JointChoice stores natural s,r,h,v in that order, with 1<=r<=s<=2^(a-1), v<2^(d-1), h<2^(b-1), inclusion of the bits of r-1 in s-1 below a-1, and nonnegativity of all twelve gates at t=2^d,z=2^c,x=2^a,y=2^b. Native constructs this record; Physical consumes it to construct the word. The record itself is an interface, not an existence assertion.

These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Structure.JointChoice`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Structure.gate`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Source](../PacketNormalForm/Source.md)
