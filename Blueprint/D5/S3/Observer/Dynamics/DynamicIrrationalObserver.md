# Dynamic Irrational Observer

## Abstract

A dynamic irrational observer has a contractive ratio and an infinite higher jet.

**Definition 1.1 (Contractive observer with an infinite jet).**

Lean statement: `D5/S3/Observer/Dynamics/DynamicIrrationalObserver.Observer`

*Formalization.* `D5/S3/Observer/Dynamics/DynamicIrrationalObserver.Observer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observer records a completed value, a contraction ratio, a linear coefficient, and a genuinely infinite family of higher coefficients indexed directly by every natural number from two onward.

A thread realizes these data when the higher-order terms have the stated infinite sum at every time. This explicit HasSum relation does not silently assign a real value to a non-summable formal series.

The zeroth readout is the completed value, the first readout is the linear coefficient, and every readout from order two is the corresponding higher coefficient.

The golden first observation class is inhabited. Its completed value is the golden ratio, its contraction is minus the inverse golden ratio squared, its linear coefficient is one, and all higher coefficients vanish; the thread is the golden ratio plus the nth power of the contraction.

The source's full-jet reconstruction sentence is not asserted as injectivity: the displayed readout sequence omits the contraction ratio, and the source gives no convergence condition for arbitrary higher coefficients.

## References

- Truth anchor: `D5/S3/Observer/Dynamics/DynamicIrrationalObserver.Observer`
- Dependency: [D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative](../../CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.md)
