# Finite Reflection-Compatible Weil Interpolation

Status: Candidate source and author projection. Kernel and Scribe reconciliation remain separate checks.

For actual zero data Z, a finite set E of indices, and complex values a satisfying a(R j)=a(j), the module constructs a compact smooth even Weil test g with FT(g)(gamma_j)=a(j) for every j in E.

The construction reuses the reflection representative and frequency-injectivity lemmas from the existing single-orbit separator. It invokes `even_weilTestFunction_finite_interpolation` on the sign quotient. It does not reconstruct the Fourier-Laplace interpolation theorem.

The constant assignment gives a simultaneous unit peak on any finite union of zero orbits.

Main declarations:

- `even_weil_interpolation_on_finite_indices`
- `exists_even_weil_finite_unit_peak`
