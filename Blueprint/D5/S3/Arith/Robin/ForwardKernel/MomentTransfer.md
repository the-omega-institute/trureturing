# Moment transfer

## Abstract

Mixed increment moment limits transfer to the original price-weighted response for every real integrable profile.

**Theorem 1.1 (Support of the dyadic probability measure).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransfer.ae_dyadic_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MomentTransfer.ae_dyadic_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real X, almost every x with respect to the dyadic probability measure at scale X lies in [X,2X].

**Theorem 1.2 (Unequal finite product moment bounds).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransfer.product_moment_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MomentTransfer.product_moment_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k positive and k real functions on a measure space, suppose each absolute kth power and the product of absolute values are integrable. If the individual kth moments are bounded by nonnegative numbers C_i, Holder bounds the integral of the product of absolute values by the product of C_i^(1/k). Almost everywhere strong measurability suffices, and zero bounds are allowed. Equal bounds give the common bound C.

**Theorem 1.3 (Joint moment transfer for a finite family of profiles).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransfer.joint_moment_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MomentTransfer.joint_moment_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive integer k, exponents e_i strictly between zero and one, and real integrable profiles G_i. If E is measurable and bounded on compact intervals, the absolute kth moments of the normalized increments are eventually uniformly bounded over every index and unit parameter, and the joint position-weighted mixed moments converge at every point of the unit cube to M, then the moment of the product of normalized profile responses converges to the cube integral of product_i G_i(s_i) times M(s).

Expand the finite product of profile integrals and apply Fubini. Generalized Holder bounds the absolute mixed increment moment by 2 raised to the sum of r(e_i), times the common moment bound. Apply the price estimate to each exponent and sum their absolute errors to obtain one vanishing error bound. Replacing all price factors by one has vanishing integral error; dominated convergence gives the remaining limit. Only measurability of the approximating kernels is needed.

**Theorem 1.4 (Moment transfer for every positive integer order).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MomentTransfer.moment_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MomentTransfer.moment_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix 0<theta<1 and a positive integer k. Suppose E is measurable and bounded on compact intervals, the integrals of |B(s,x)|^k against the dyadic logarithmic probability measure are eventually bounded by one constant C uniformly for 0<=s<=1, and the position-weighted mixed moments converge pointwise on the unit cube to a measurable function M. Then for every real L1 profile g, the kth moment of the original normalized price-weighted response converges to the integral of product_i g(s_i)*M(s) over the k-dimensional unit cube.

Apply joint moment transfer to the constant exponent and constant profile families. Their joint increment moments equal the original mixed moments, and the product of normalized responses is the kth power.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransfer.ae_dyadic_mem`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransfer.joint_moment_transfer`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransfer.moment_transfer`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MomentTransfer.product_moment_bound`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MomentTransferWeights](MomentTransferWeights.md)
