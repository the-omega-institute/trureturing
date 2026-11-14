# Discrete interval and no-carry tools for the diagonal

## Abstract

Cyclic residue selection without enumeration

**Lemma 1.1 (Hit a permitted residue interval).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/CyclicArithmetic.cyclic_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/CyclicArithmetic.cyclic_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For G>=2,m>=2 and (2Gm+1) not dividing tau, cyclic_cover constructs integers n,l with -2G<=n<2G, Gm-m<=l<=Gm-2 and divisibility of tau+Gm-1+nm-l. euclidean_gap_hit supplies the discrete gap argument, including its excluded residue; no real rotation or sampled orbit is used.

**Lemma 1.2 (Equality residue including the wrap).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/CyclicArithmetic.equality_residue`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/CyclicArithmetic.equality_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For g>=1 the shifted residue interval -1<=n<g contains a solution to (g+1) dividing tau+1+n. odd_successor_not_dvd_pow excludes divisibility of a power of two by 2^c+1 for c>=1. native_hr recovers native h,r and scaled_rectangle interpolates the separately affine h,r margins. These facts are consumed by GeneralArithmetic.selected_rectangle.

These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/CyclicArithmetic.cyclic_cover`
- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/CyclicArithmetic.equality_residue`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/Certificates](Certificates.md)
