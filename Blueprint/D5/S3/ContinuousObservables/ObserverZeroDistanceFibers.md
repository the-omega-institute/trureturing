# Observer Zero-Distance Fibers

## Abstract

Unit-ball spanning identifies observer fibers with zero-distance classes.

**Theorem 1.1 (Readout fibers are exactly the zero-distance classes).**

$$\forall X \in Type, A \in \operatorname{Submodule}\left(\mathbb{R}, \operatorname{ellInfty}\left(X, \mathbb{R}\right)\right), L \in A \to [0, \infty],\; \left(\left(\forall c \in \mathbb{R}, f \in A,\; L\left(\operatorname{smul}\left(c, f\right)\right) = \left|c\right| \cdot L\left(f\right)\right) \land \operatorname{span}\left(\mathbb{R}, \operatorname{unitBall}\left(A, L\right)\right) = A\right) \Rightarrow \left(\left(\forall rho \in X, sigma \in X,\; \operatorname{observerDistance}\left(A, L, rho, sigma\right) = 0 \Leftrightarrow \left(\forall f \in A,\; f\left(rho\right) = f\left(sigma\right)\right)\right) \land \left(\left(\forall rho \in X,\; \left\{\forall f \in A,\; f\left(rho\right) = f\left(sigma\right) \mid sigma \in X\right\} = \left\{\operatorname{observerDistance}\left(A, L, rho, sigma\right) = 0 \mid sigma \in X\right\}\right) \land \left(\left(\left(\forall rho \in X, sigma \in X,\; \left(\forall f \in A,\; f\left(rho\right) = f\left(sigma\right)\right) \Rightarrow rho = sigma\right) \Rightarrow \left(\forall rho \in X, sigma \in X,\; \operatorname{observerDistance}\left(A, L, rho, sigma\right) = 0 \Rightarrow rho = sigma\right)\right) \land \left(\left(\exists rho \in X, sigma \in X,\; rho \ne sigma \land \left(\forall f \in A,\; f\left(rho\right) = f\left(sigma\right)\right)\right) \Rightarrow \left(\exists rho \in X, sigma \in X,\; rho \ne sigma \land \operatorname{observerDistance}\left(A, L, rho, sigma\right) = 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/ObserverZeroDistanceFibers.observer_zero_distance_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen unit-ball spanning criterion supplies the zero-distance equivalence. Set extensionality gives the fiber identity; point separation and a hidden-kernel pair give the two endpoint consequences.

## References

- Truth anchor: `D5/S3/ContinuousObservables/ObserverZeroDistanceFibers.observer_zero_distance_fibers`
- Dependency: [D5/S3/ContinuousObservables/DualObserverDistanceReadings](DualObserverDistanceReadings.md)
