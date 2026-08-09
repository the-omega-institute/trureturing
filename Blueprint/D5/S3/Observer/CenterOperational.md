# Operational Characterization of the Center

## Abstract

The operational center of a finite cyclic observer window consists exactly of constant observables.

**Theorem 1.1 (Zero perturbation characterizes the operational center).**

$$\begin{gathered}\forall M\in \mathbb{N}_{>0},\\\forall f: \operatorname{ZMod}(M)\to \mathbb{C},\\L_{+1}(f)= 0 \Leftrightarrow \exists c\in \mathbb{C},\ f= (i\mapsto c).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CenterOperational.center_iff_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be positive and let f be a complex-valued observable on the cyclic window ZMod M. The seminorm L for translation by one measures the largest pointwise update defect. Its kernel is the operational center considered here.

The established seminorm-kernel theorem first identifies zero perturbation with invariance under translation by one. The existing update-defect equivalence transfers that condition to zero defect, and the cyclic-window characterization then gives a scalar c for which f is the constant function with value c. Conversely, every constant observable lies in the kernel. The result introduces no larger operator algebra or independent notion of center.

## References

- Truth anchor: `D5/S3/Observer/CenterOperational.center_iff_const`
- Dependency: [D5/S3/Observer/ObserverMetric](ObserverMetric.md)
