---
bibkey: vonluxburg2007spectralclustering
authors: Ulrike von Luxburg
year: 2007
title: A Tutorial on Spectral Clustering
doi: 10.1007/s11222-007-9033-z
url: https://arxiv.org/abs/0711.0189
claim: "For a finite undirected graph with symmetric nonnegative weights, the unnormalized Laplacian is symmetric positive semidefinite and its kernel is spanned by the positive-weight component indicators."
strata_touched: []
license: citation-only
triage: anchor
---

# Weighted Laplacian kernel and mean-zero inverse

The [primary text](https://arxiv.org/pdf/0711.0189), Section 2.1, printed
p. 2, specifies symmetric nonnegative weights and treats a zero weight as
absence of an edge. Section 3.1, Propositions 1–2, printed pp. 4–5, gives
the quadratic energy, symmetry, positive semidefiniteness and the kernel
spanned by connected-component indicators. Connectivity refers to the
positive-weight graph. Section 6, “The commute distance,” printed p. 15, defines the pseudoinverse
by replacing positive eigenvalues by their reciprocals and leaving zero
eigenvalues zero.

For a connected graph, these facts and the symmetric image–kernel
orthogonality give solvability of the centered Poisson equation and a
unique mean-zero potential. With incidence columns equal to head minus
tail, the consumer uses the unnormalized matrix
$L=B\operatorname{diag}(k_e)B^{\mathsf T}$; its inverse on constants is zero.
For disconnected graphs, compatibility and the potential gauge are
componentwise. These are classical intermediate inputs to the
[five-state seam-field response](../../docs/develop/theory/AURIC_FIB_ATOM_STATIC_SEAMS_TRANSITION_CIRCULATION_AND_FIBONACCI_TOGGLE_CYCLES.md),
Sections 10 and 12. The extraction of local probability laws, the source
functional and exponential clock response are separately specified model
data. No physical gravity or continuum limit is supplied by this citation.
