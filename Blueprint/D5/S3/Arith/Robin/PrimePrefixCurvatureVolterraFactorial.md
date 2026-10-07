# Exact Factorial Errors for the Actual Curvature Recursion

## Abstract

The actual Volterra recursion has its exact 3n-factorial residual bound and recovers the literal Phi curvature uniformly on each nonnegative compact interval.

Retain the same actualPhi, curvature(v)=deriv(deriv actualPhi)(v), coefficient a, positive Volterra operator T, recursive approximations Bn and residuals Rn=curvature-Bn from PrimePrefixCurvatureVolterraRecursion.

**Theorem 1.1 (The exact residual rate and compact uniform recovery).**

Lean statement: `D5/S3/Arith/Robin/PrimePrefixCurvatureVolterraFactorial.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimePrefixCurvatureVolterraFactorial.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and every v>=0, Rn(v)>=0 and abs(Rn(v))<=v^(3*n)/(2*3^n*(3*n)!). The n=0 bound is exactly 1/2, including v=0; the bound gives Rn(0)=0 for every positive n. No positive-axis assumption excludes the zero endpoint.

For every V>=0 and every v in [0,V], the same error is at most V^(3*n)/(2*3^n*(3*n)!). Consequently Rn tends uniformly to zero on [0,V], and Bn tends uniformly to the original curvature there. Both actual pointwise limits hold for every v>=0.

A continuous finite-integral model equals the original curvature on the entire nonnegative axis. Its actual T iterates equal the original residuals, using the preceding public result and finite-integral congruence. The model supplies integrability without replacing the curvature or repeating its derivative chain. The original curvature bound is consumed from PrimePrefixPhiCurvature.result.

The normalized monomial t^d/d! lifts exactly to v^(d+2)/(d+2)!. Since 0<a<=1/3 and exp(-v)<=1, the actual T maps the corresponding nonnegative bound with factor M to factor M/3 and degree d+3. Induction with d=3*n gives the exact constant 2*3^n*(3*n)!. The auxiliary inequality n!<=(3*n)! is used only to prove that this exact rate tends to zero through Mathlib's factorial limit.

The private consumed factorial-integral helper is copied from OpenAI math contributors, lean/OAI/Analysis/VlasovMaxwell/Regularity/VolterraSup.lean at revision adc7f1241b42e322a6451854ab7e4b4c146bf78a, under Apache License Version 2.0. Its upstream proof body is retained with private visibility. Actual finite-integral continuity and congruence helpers retain PrimePrefixCurvatureVolterraRecursion provenance. Mathlib supplies interval comparison, compact uniform convergence and factorial limits. Complete logarithmic-moment convergence, the same-source signed Robin transport and the RH endpoint remain separate open obligations.

## References

- Truth anchor: `D5/S3/Arith/Robin/PrimePrefixCurvatureVolterraFactorial.result`
- Dependency: [D5/S3/Arith/Robin/PrimePrefixCurvatureVolterraRecursion](PrimePrefixCurvatureVolterraRecursion.md)
