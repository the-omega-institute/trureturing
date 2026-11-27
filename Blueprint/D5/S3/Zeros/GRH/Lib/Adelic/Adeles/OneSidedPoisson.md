# One Sided Poisson

## Abstract

One Sided Poisson

self-duality of a number field in its adeles, strong approximation, and the Poisson inequality. The file treats totally complex fields, for which the field is its own annihilator and the pairing is non-degenerate. Strong approximation omitting a nonempty set of finite places is deduced from duality, and Poisson summation is an inequality for nonnegative lower semicontinuous functions. Source: J. Tate, Fourier analysis in number fields and Hecke's zeta-functions, thesis 1950, in Cassels-Fröhlich ch. XV, Theorem 4.1.4; for strong approximation, Cassels, ch. II §15.

**Theorem 1.1 (sum_le_of_fourier).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Adelic/Adeles/OneSidedPoisson.sum_le_of_fourier`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Adelic/Adeles/OneSidedPoisson.sum_le_of_fourier` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

One-sided Poisson summation on the adeles of E: let F ≥ 0 be integrable and lower semicontinuous at the points of a finite set T ⊂ E. If S bounds all finite sums of |∫ ψ(−ξx)F(x) dx| over ξ in E, then ∑_{t∈T} F(t) ≤ S.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Adelic/Adeles/OneSidedPoisson.sum_le_of_fourier`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/Adeles/AdeleSelfDual](AdeleSelfDual.md)
