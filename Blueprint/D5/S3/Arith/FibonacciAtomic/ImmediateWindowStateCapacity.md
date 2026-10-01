# Immediate Fibonacci Window Readout Kernel

## Abstract

The consecutive three-bit window readouts have an exact determinant-two kernel.

**Theorem 1.1 (The kernel is exactly the two-torsion in the first coordinate).**

$$\forall m \in \operatorname{N}(), \forall x \in \operatorname{ZMod}(m)\times\operatorname{ZMod}(m), \\(\operatorname{windowObserve}(x) = 0) \Leftrightarrow \exists a \in \operatorname{ZMod}(m), (x = (a, 0)) \land (2a = 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.window_observe_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a modulus m, the two readouts are q x and q S x, with q=(2,3) and S=[[1,2],[2,3]].

Subtracting four times the first readout from the second leaves the second composition coordinate. The first readout then leaves twice the first coordinate, so the kernel is precisely the stated two-torsion family.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity.window_observe_kernel`
