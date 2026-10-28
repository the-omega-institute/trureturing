# Original Selected Normalizer Cap

## Abstract

The complete label window bounds the full selected volume and literal kernel mass.

**Theorem 1.1 (A global label budget for the complete selected source union).**

Lean statement: `D5/S3/Arith/Robin/OriginalSelectedNormalizerCap.original_selected_normalizer_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalSelectedNormalizerCap.original_selected_normalizer_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be any OriginalWindow and put L=X.labelStart. The only additional hypothesis is 0<=L. The labels are all primes in originalLabelWindow(L), and canonicalSource(p) is the least attained maximizer of the original nonlinear objective over all positive integers divisible by 5040p. Let S=selectedDomain(X), the union of the closed source-clock intervals of every actual GoodEdge. All original labels and all qualifying edges are retained, including the strict inventory condition at both endpoints.

The conclusion is volume.real(S)<=L and, for every real x with 4<=x, 0<=integral over S of kernel(t,x)<=x^(-3/10)L. The kernel is exactly OriginalMovingWindowMoment.kernel, with width(t)=t^(4/5), endpoint(t)=t+width(t), strict initial exclusion t<x and weak terminal inclusion x<=endpoint(t). No clock ordering for all labels, lower clock hypothesis, R<p_0 bound, or Fin(n+1) enumeration is assumed.

Each good edge (p,r) has one positive integer U with 5040 dividing U and canonicalSource(p)=pU, canonicalSource(r)=rU. Its source interval therefore has length log(r)-log(p). Consecutive-label intervals (log(p),log(r)] are pairwise disjoint and lie in (L,2L]. Their total length is at most L. The source intervals may overlap: finite union subadditivity, rather than source disjointness, transfers that budget to S. Empty and singleton label sets require no separate enumeration.

The actual 5040 inventory and prime label imply every selected source clock is at least four. On active support, price_drop bounds the kernel by (endpoint(t)-x)/t^(11/10). Set d=x-t. Since 0<=d<=width(t)<=t, (width(t)-d)(1+d/t)<=width(t). Also x^(3/10)<=t^(3/10)(x/t). Combining these estimates gives kernel(t,x)<=x^(-3/10); outside the support the kernel is zero. The existing interval integrability theorem extends to the finite union, so integrating the pointwise estimate and consuming volume.real(S)<=L gives the stated literal mass bound.

This is an absolute upper bound and permits S to be empty. It supplies no positive selected mass, qualifying cofinal family, relative normalizer transfer, favorable signed moment, or RH conclusion. The selected-kernel definitions and comparison hypotheses of the selected Euler-layer theory remain distinct from this global label-budget estimate.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalSelectedNormalizerCap.original_selected_normalizer_cap`
- Dependency: [D5/S3/Arith/Robin/OriginalFirstClockTransport](OriginalFirstClockTransport.md)
- Dependency: [D5/S3/Arith/Robin/OriginalMovingCutRow](OriginalMovingCutRow.md)
