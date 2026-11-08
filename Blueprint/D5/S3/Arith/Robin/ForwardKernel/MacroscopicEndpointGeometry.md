# Macroscopic endpoint geometry

## Abstract

Shared endpoint geometry for macroscopic freezing

**Theorem 1.1 (Derivative and image bounds for moving endpoints).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicEndpointGeometry.macro_endpoint_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MacroscopicEndpointGeometry.macro_endpoint_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a be a nonnegative C1 function on [1,2], bounded by M with absolute derivative at most L. For X>0 and X<=l<=r<=2X, choose c in [0,M]. Assume M*X^theta<=X and L*X^theta/X<=1/2. On [l,r] the frozen endpoint p(x)=x+X^theta*c has derivative one, while the moving endpoint q(x)=x+X^theta*a(x/X) has derivative 1+X^theta*a'(x/X)/X, at least one half. Both endpoints are continuous and take values in [l,r+M*X^theta]. The derivatives are taken within the closed interval, so only regularity of a on [1,2] is needed.

**Theorem 1.2 (The endpoint gap on one equal cell).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicEndpointGeometry.macro_cell_gap_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/MacroscopicEndpointGeometry.macro_cell_gap_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a be a nonnegative C1 function on [1,2], bounded by M with absolute derivative at most L>=0. For X>0, n>0 and j<n, write u_j=1+j/n. Every x in [u_j*X,u_(j+1)*X] satisfies |X^theta*(a(x/X)-a(u_j))|<=X^theta*L/n. The mean value inequality applies within [1,2], and the macroscopic cell width is exactly 1/n.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicEndpointGeometry.macro_cell_gap_le`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/MacroscopicEndpointGeometry.macro_endpoint_geometry`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/MacroscopicVarianceDefs](MacroscopicVarianceDefs.md)
