# Character sums of cyclic Fourier projection ensembles

## Abstract

The squared-minor law turns cyclic Fourier column overlaps into exact second moments.

**Definition 1.1 (Selected cyclic Fourier columns).**

Lean statement: `D5/S3/Analytic/Oscillation/CyclicProjectionMoments.selectedColumns`

*Formalization.* `D5/S3/Analytic/Oscillation/CyclicProjectionMoments.selectedColumns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a positive integer M, an embedding a of k indices into Z/MZ selects the columns. The row indexed by x and the column indexed by i have entry s times the standard additive character at a(i)x, where s is a complex scaling factor.

**Theorem 1.2 (Second moment of a cyclic character sum).**

Lean statement: `D5/S3/Analytic/Oscillation/CyclicProjectionMoments.cyclic_projection_second_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Oscillation/CyclicProjectionMoments.cyclic_projection_second_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be the image of the selected columns and choose s with s times its conjugate equal to 1/M. On each k-element subset X of the M sites, the probability is the squared modulus of its row minor. Sum the r-th cyclic character over X. The expectation of the squared modulus of this sum is k plus k squared at r=0, minus the number of a in A for which a-r also belongs to A.

The diagonal site pairs contribute k. For distinct sites the squared-minor inclusion formula uses a product of two diagonal projection entries minus the product of conjugate entries. Expanding the latter and summing both site characters leaves exactly the ordered column pairs whose difference is r.

This is a finite expectation at cyclic frequencies. A statement about one deterministic spectrum, all real cutoff heights or Lorentz-weighted pair correlations needs additional estimates.

## References

- Truth anchor: `D5/S3/Analytic/Oscillation/CyclicProjectionMoments.cyclic_projection_second_moment`
- Truth anchor: `D5/S3/Analytic/Oscillation/CyclicProjectionMoments.selectedColumns`
- Dependency: [D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap](../../Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.md)
