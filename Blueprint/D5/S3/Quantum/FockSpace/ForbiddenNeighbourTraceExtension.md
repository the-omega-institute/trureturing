# Forbidden-Neighbour Trace and Extension

## Abstract

Nonnegative bidiagonal weights have fixed trace and zero-tail extension rigidity.

L_w is the actual square-root lower-bidiagonal matrix: its diagonal entry i is sqrt(w(2i)), and its entry below that diagonal is sqrt(w(2i+1)). C_w is the actual forbidden-neighbour configuration polynomial. Indices below start at zero. All real weights may vanish or repeat.

**Theorem 1.1 (The trace counts every weight).**

$$\forall d\in \mathbb{N},d\ge 1:w\in \mathbb{R}^{2d-1},(\forall j:w_{j}\ge 0)\implies \operatorname{Tr}(L_{w}L_{w}^{T})=\sum_{j=0}^{2d-2}w_{j}\land \operatorname{Tr}(L_{w}^{T}L_{w})=\sum_{j=0}^{2d-2}w_{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/ForbiddenNeighbourTraceExtension.lower_bidiagonal_trace_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace of L_w L_w^T is the sum of its squared entries. Splitting diagonal and subdiagonal entries enumerates the even and odd weight indices exactly once. Nonnegativity justifies sqrt(w)^2=w. Cyclicity gives the same trace for L_w^T L_w.

**Theorem 1.2 (Two appended weights vanish).**

$$\begin{aligned}\forall d\in \mathbb{N},d\ge 1:w\in \mathbb{R}^{2d-1},u\in \mathbb{R}^{2d+1}\\(\forall j:u_{j}\ge 0)\land (\forall 0\le j\le 2d-2:u_{j}=w_{j})\land \sum_{j=0}^{2d}u_{j}=\sum_{j=0}^{2d-2}w_{j}\implies\\u_{2d-1}=0\land u_{2d}=0\land L_{u}=\operatorname{diag}(L_{w},0)\land C_{u}=C_{w}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/ForbiddenNeighbourTraceExtension.unchanged_weights_zero_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum splits into the unchanged prefix and its last two nonnegative entries, so both last entries are zero. The displayed direct sum means reindexing L_u by finSumFinEquiv from Fin d plus Fin 1: the old block is L_w and every new entry is zero. The public endpoint recurrence applied twice then gives C_u=C_w. This includes d=1. No unchanged-block claim is made for L_u^T L_u before the appended weights vanish.

## References

- Truth anchor: `D5/S3/Quantum/FockSpace/ForbiddenNeighbourTraceExtension.lower_bidiagonal_trace_weights`
- Truth anchor: `D5/S3/Quantum/FockSpace/ForbiddenNeighbourTraceExtension.unchanged_weights_zero_append`
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant](ForbiddenNeighbourDeterminant.md)
