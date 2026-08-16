# Backward Orbit Core

## Abstract

Infinite backward trajectories of a finite self-map are exactly its periodic core.

**Theorem 1.1 (Backward orbits are the periodic core).**

$$\forall Y, [\operatorname{Finite} Y],\ F: Y \to Y,\ \operatorname{Bijective}(ev_{0}: B(F) \to P(F)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/BackwardOrbitCore.backward_orbit_eval_zero_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite carrier and F a self-map. A backward orbit is a sequence x indexed by the natural numbers with F(x(n+1))=x(n). Its coordinate-zero evaluation lands in the positive-period points of F.

Coordinate-zero evaluation is bijective. Surjectivity follows because F is a bijection on its periodic core, so every periodic point has a unique infinite chain of periodic predecessors. Injectivity uses a finite pigeonhole collision to show that every coordinate of any backward orbit is periodic, where F is injective.

Pinned Mathlib and Loogle supplied Function.bijOn_periodicPts, Function.IsPeriodicPt.eq_of_apply_eq, and the finite pigeonhole theorem used by the proof. Pinned-Mathlib, repository, and GitHub Lean-source searches found no full inverse-limit equivalence. LeanSearch's API endpoint returned HTTP 404 and supplied no search conclusion.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/BackwardOrbitCore.backward_orbit_eval_zero_bijective`
