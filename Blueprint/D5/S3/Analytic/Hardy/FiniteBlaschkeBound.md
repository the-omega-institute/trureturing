# Finite Blaschke bound in the open disk

## Abstract

Finite Blaschke bound in the open disk

**Theorem 1.1 (Bound by the product of pseudohyperbolic distances).**

$$\left\lVert f\left(z\right) \right\rVert \le M \prod_{k\in s} \left\lVert \frac{z-a_{k}}{1-\overline{a_{k}} z} \right\rVert$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hardy/FiniteBlaschkeBound.norm_le_mul_prod` (`✓ std3`). ∎

*Citation.* John B. Garnett (2007). *Bounded Analytic Functions*. DOI: [10.1007/0-387-49763-3](https://doi.org/10.1007/0-387-49763-3). URL: <https://link.springer.com/book/10.1007/0-387-49763-3>.

*Commentary.*

Let s be a finite set of indices and a an injective complex-valued family. Let f be holomorphic and bounded in norm by M on the open unit disk. If aₖ is in the disk and f(aₖ)=0 for every k in s, the displayed estimate holds at each z in the disk. An empty product is one.

On a smaller closed disk containing the point and all specified zeros, divide out one disk factor at a time. Divided differences remove the singularity at each zero. Mathlib's canonical disk factors have unit modulus on the boundary circle, so the maximum modulus principle preserves M after each division. Taking the radii up to one gives the bound with the unit-disk factors.

## References

- Truth anchor: `D5/S3/Analytic/Hardy/FiniteBlaschkeBound.norm_le_mul_prod`
