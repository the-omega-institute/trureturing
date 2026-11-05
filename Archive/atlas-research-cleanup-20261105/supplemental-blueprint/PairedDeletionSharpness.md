# Sharpness of Overlapping Paired-Deletion Stability

## Abstract

For every finite support with at least four labels and every three distinct supported labels a, b, c, there are two genuine probability measures on legal oriented cycles whose source total variation is one while the two overlapping paired-deletion readouts `(D_a,D_b)` and `(D_b,D_c)` each retain total variation exactly one third. The construction is carried by six actual rotation classes, so the obstruction lives in the circular deletion geometry rather than in an abstract six-state proxy.

**Theorem 1.1 (Native real-law sharpness and coefficient obstructions).**

Let `A` be a finite support with `4 ≤ card A`, and let `a`, `b`, and `c` be pairwise distinct elements of `A`. There is a nonempty nodup list `L` enumerating `A \ {a,b,c}` and a finite legal carrier of actual cycles on `A` with native real probability measures `ρ` and `σ` such that

```
TV(ρ, σ) = 1,
TV((D_a,D_b)_*ρ, (D_a,D_b)_*σ) = 1/3,
TV((D_b,D_c)_*ρ, (D_b,D_c)_*σ) = 1/3.
```

Consequently every universal inverse inequality on this carrier of the form

```
TV(m,n) ≤ K · ( TV(F_*m,F_*n) + TV(G_*m,G_*n) )
```

has `K ≥ 3/2`, and every inequality with the maximum of the two readout errors has `K ≥ 3`.

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/PairedDeletionSharpness.real_probability_paired_deletion_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the six actual cycles

```
C   = [a,b,c,L]       CF = [b,a,c,L]       CG = [a,c,b,L]
E   = [c,b,a,L]       EF = [c,a,b,L]       EG = [b,c,a,L].
```

The first law puts mass `1/3` on `CF`, `CG`, and `E`; the second puts mass `1/3` on `C`, `EF`, and `EG`. A rooted insertion argument proves that these are six distinct rotation classes and that every class has support exactly `A`.

For `F=(D_a,D_b)`, the pairs from `CF` and `C` coincide, as do the pairs from `E` and `EF`; after cancellation the signed difference is a dipole of two distinct output atoms, `F(CG)` and `F(EG)`, with weights `±1/3`. Thus its total variation is `1/3`. The same calculation for `G=(D_b,D_c)` cancels `CG` with `C` and `E` with `EG`, leaving the distinct dipole `G(CF)-G(EF)`.

The Lean theorem constructs `ρ` and `σ` with the repository's native `ProbabilityMeasure` and real finite half-ℓ¹ total variation. It proves the carrier legality, source injectivity, all four deletion identities and survivor inequalities, then derives both coefficient lower bounds by substituting the same two native laws into the proposed universal inequality. The proof uses only the standard kernel closure `propext`, `Classical.choice`, and `Quot.sound`.

This is a lower-bound sharpness result. It does not by itself assert a matching upper bound for arbitrary paired-deletion channels or classify all possible fibres.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/PairedDeletionSharpness.real_probability_paired_deletion_sharpness`
- Dependency: [D5/S3/Combinatorics/CircularWords/PairedDeletionFiber](PairedDeletionFiber.md)
- Dependency: [D5/S3/Combinatorics/CircularWords/CircularDeletionTransport](CircularDeletionTransport.md)
