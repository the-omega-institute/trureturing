# A Mellin-Barnes residue series

## Abstract

Closing a contour sequence identifies its integral with the summable residue series.

**Theorem 1.1 (The residue HasSum).**

$$\forall F \in Complex \to Complex,\; \forall c \in Nat \to Real,\; \forall p \in Nat \to Complex,\; \forall phi \in Nat \to \left(Complex \to Complex\right),\; \left(MBSeriesData\left(F, c, p, phi\right) \land \left(Tendsto\left((n:Nat \mapsto integral\left((y:Real \mapsto F\left((c\left(n\right)+(y*\operatorname{ComplexI}))\right))\right)), atTop, nhds\left(0\right)\right) \land Summable\left((n:Nat \mapsto phi\left(n, p\left(n\right)\right))\right)\right)\right) \Rightarrow HasSum\left((n:Nat \mapsto ((2*\pi )*(n:Nat \mapsto phi\left(n, p\left(n\right)\right))\left(n\right))), integral\left((y:Real \mapsto F\left((c\left(0\right)+(y*\operatorname{ComplexI}))\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/MellinBarnesSeries.mbSeries_hasSum` (`✓ std3`). ∎

*Citation.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

MBSeriesData retains all seven obligations: the pole lies between consecutive lines; each numerator is holomorphic on its closed strip; the actual integrand equals that numerator divided by s-p away from the pole; every line is integrable; and the horizontal cross-sections vanish at both ends. Iterating the single-pole shift telescopes the line integrals. The moving-left limit and residue summability then identify the integral by HasSum uniqueness. The Mittag-Leffler identity supplies every obligation for its literal kernel.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/MellinBarnesSeries.mbSeries_hasSum`
- Dependency: [D5/S3/Analytic/Asymptotics/BarnesResidue](BarnesResidue.md)
