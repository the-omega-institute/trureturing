# Sharpness of Overlapping Paired-Deletion Stability

## Abstract

For every finite support with at least four labels and every three distinct supported labels, native real probability laws on actual cycles attain source total variation one and paired-deletion readout total variations one third on each of two overlapping channels.

For every finite support with at least four labels and every three distinct supported labels a, b, c, there are two genuine probability measures on legal oriented cycles whose source total variation is one while the two overlapping paired-deletion readouts (D_a,D_b) and (D_b,D_c) each retain total variation exactly one third. The construction is carried by six actual rotation classes.

**Theorem 1.1 (Native real-law sharpness and coefficient obstructions).**

$$(\mathrm{TV}\left(rho, sigma\right) = 1) \land ((\mathrm{TV}\left(\mathrm{Fstar}\left(rho\right), \mathrm{Fstar}\left(sigma\right)\right) = \frac{1}{3}) \land (\mathrm{TV}\left(\mathrm{Gstar}\left(rho\right), \mathrm{Gstar}\left(sigma\right)\right) = \frac{1}{3}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/PairedDeletionSharpness.real_probability_paired_deletion_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the six actual cycles C=[a,b,c,L], CF=[b,a,c,L], CG=[a,c,b,L], E=[c,b,a,L], EF=[c,a,b,L], and EG=[b,c,a,L]. The first law puts mass one third on CF, CG, and E; the second puts mass one third on C, EF, and EG. A rooted insertion argument proves that these are six distinct rotation classes and that every class has support exactly A.

For F=(D_a,D_b), the pairs from CF and C coincide, as do the pairs from E and EF; after cancellation the signed difference is a dipole of two distinct output atoms with weights plus or minus one third. The same calculation for G=(D_b,D_c) cancels CG with C and E with EG. Substitution into a universal sum or maximum inverse inequality gives K at least 3/2 or 3.

The theorem uses native ProbabilityMeasure values and the repository's real finite half-l1 total variation. It is a lower-bound sharpness result; a matching general upper bound is a separate question.

The proof has standard kernel axiom closure only: propext, Classical.choice, and Quot.sound.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/PairedDeletionSharpness.real_probability_paired_deletion_sharpness`
- Dependency: [D5/S3/Combinatorics/CircularWords/CyclicInsertionGap](CyclicInsertionGap.md)
- Dependency: [D5/S3/Estimation/DataProcessing/NativeDeclaredProbabilityPolytope](../../Estimation/DataProcessing/NativeDeclaredProbabilityPolytope.md)
- Dependency: [D5/S3/TotalVariation/Metric](../../TotalVariation/Metric.md)
