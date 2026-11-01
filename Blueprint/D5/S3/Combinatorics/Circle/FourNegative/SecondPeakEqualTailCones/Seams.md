# One allocation matrix for both source rows

## Abstract

Doubled cumulative seam gates

Use source heads (A,B,L,M), enlarged heads (2A,Bn,Ln,Mn), and terminal order W,U,X,V. For u=z/2-1, capacities h,f,e and allocations p,c, the four bank rows in chain order U,V,W,X are (u,0,p,0), (0,u,h-p,c), (0,0,f-h,0) and (0,0,0,e-c). A dot product with either head vector gives the corresponding positive mass.

The first doubled postterminal seam is twice bank 1 mass plus the W successor minus the row modulus. The second adds twice bank 2 mass and the U terminal. The third adds bank 3 and the X terminal; in the enlarged row it also adds the true fresh contribution 2A. Thus these seams are cumulative prefixes, not individual bank increments. For each of the first three seams the four gates are the old seam, old successor minus 1 minus that seam, the new seam, and new successor minus 1 minus that seam.

All twelve nonnegative gates bound both rows at the required terminal interfaces. The final bank returns both doubled sums exactly to zero by the eight source recurrences and 2(u+1)=z, 2(f+1)=y, 2(e+1)=x. This algebra is shared by the native upper allocation and the lower-cone ceiling allocation; positivity and physical inventory are separate obligations.

## References

- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Native](Native.md)
