# Banks

## Abstract

Third peak second A full cone: Banks

The bank words are literal lists of physical labels. A1 and A2 use complement V(h-1), full W, V(h-H), complement or f-masked X, full U, and the remaining V/X masks. B0 and B1 use m=j-1, R=qj, f=3x/(4t), and both B1 delta branches: delta=1 when R<xy, delta=R/(xy) otherwise, including equality. C uses terminal order X,W,V,U and the first positive X insertion location. For nested powers 2^v<=2^u and 0<=delta<2^v, the three masks full XOR (2^u-1), 2^u-2^v+delta, and (2^v-1) XOR delta partition the physical bank. The positive stock omits all four terminal labels d-1,d+c-1,d+c+b-1,k-1. The terminals themselves are separate members of the negative inventory.

**Theorem 1.1 (labels_band_split).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Banks.labels_band_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Banks.labels_band_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

private theorem labels_band_split (len off u v delta : Nat) (hvu : v<=u) (hdelta : delta<2^v) : exact three-way physical mask partition

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Banks.labels_band_split`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakSecondAFull/Parameters](Parameters.md)
