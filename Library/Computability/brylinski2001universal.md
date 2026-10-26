---
bibkey: brylinski2001universal
authors: Jean-Luc Brylinski; Ranee Brylinski
year: 2001
title: Universal quantum gates
doi: null
url: https://arxiv.org/abs/quant-ph/0108062v1
claim: A diagonal two-qudit gate preserves all product states exactly when every phase rectangle vanishes modulo two pi; an imprimitive gate together with all one-qudit gates is exactly universal.
strata_touched: []
license: citation-only
triage: anchor
---

# Mixed phases and exact gate generation

## Verified source scope

In [arXiv:quant-ph/0108062v1](https://arxiv.org/html/quant-ph/0108062v1), Definition 1.2 distinguishes dense universality from exact finite-product universality. Theorem 1.3 proves that, when **all** one-qudit unitary gates are supplied, adding a two-qudit gate gives either form of universality precisely when that gate is imprimitive: it sends some product vector to a nonproduct vector. Proposition 2.1 specializes the product-preservation condition to diagonal gates: all phase rectangles must vanish modulo $2\pi$. These statements and their proofs are available in the cited full text.

Theorem 1.4 also allows a product-preserving gate to be a tensor product followed by SWAP. Consequently, failure to be a tensor product alone is not a general entangling criterion. The diagonal case below has the stronger explicit factorization.

## Two-qubit phase rectangle

Let $U_\phi|ab\rangle=e^{i\phi_{ab}}|ab\rangle$ for $a,b\in\{0,1\}$, and set

$$
\alpha=\phi_{10}-\phi_{00},\qquad
\beta=\phi_{01}-\phi_{00},\qquad
\Theta=\phi_{11}-\phi_{10}-\phi_{01}+\phi_{00}\pmod{2\pi}.
$$

The elementary two-qubit specialization of Proposition 2.1 is

$$
U_\phi=e^{i\phi_{00}}
\left[\operatorname{diag}(1,e^{i\alpha})\otimes
\operatorname{diag}(1,e^{i\beta})\right]
\exp(i\Theta n_1n_2),\qquad n=|1\rangle\langle1|.
$$

Checking the four basis vectors proves the equality. In particular, vanishing $\Theta$ gives local factorization. Conversely, $U_\phi|++\rangle$ has coefficient matrix

$$
M=\frac12\begin{pmatrix}
e^{i\phi_{00}}&e^{i\phi_{01}}\\
e^{i\phi_{10}}&e^{i\phi_{11}}
\end{pmatrix},\qquad
\det M=\frac{e^{i(\phi_{01}+\phi_{10})}}4(e^{i\Theta}-1).
$$

A pure bipartite vector is a product exactly when its coefficient matrix has rank one. Thus $\Theta\not\equiv0$ gives Schmidt rank two and rules out local factorization. This is an established phase-rectangle argument, not a new entanglement test.

For a declared encoder $U_{\theta,f}|ab\rangle=e^{i\theta f(a,b)}|ab\rangle$, its invariant is

$$
\Theta=\theta\,[f(1,1)-f(1,0)-f(0,1)+f(0,0)]\pmod{2\pi}.
$$

The raw real mixed difference need not vanish when the encoded gate is local: $f(a,b)=4ab$ and $\theta=\pi/2$ produce the identity. A discrete second difference also does not require analytic nonsmoothness; the polynomial $f(x,y)=xy$ has mixed difference one on the unit square.

## Exact elementary decompositions and scalar scope

[Barenco et al., *Elementary gates for quantum computation*](https://arxiv.org/pdf/quant-ph/9503016), arXiv:quant-ph/9503016v1, abstract and §§4–8, prove finite-product universality of all one-qubit $U(2)$ gates with controlled-NOT. Lemma 4.1 supplies the single-qubit Euler parametrization. The published article is *Physical Review A* 52, 3457–3467, DOI [10.1103/PhysRevA.52.3457](https://doi.org/10.1103/PhysRevA.52.3457). This note uses its exact decomposition result, not only a density statement or a finite discrete approximation theorem.

If only all single-qubit $SU(2)$ gates and CNOT are supplied, the same finite decomposition realizes every two-qubit **unitary channel**: replace each $U(2)$ factor by a scalar times an $SU(2)$ factor and collect the scalars into the unobservable overall phase. This does not supply an arbitrary relative phase between a logical subspace and a separately accessible orthogonal sector. Brylinski §9 explicitly distinguishes determinant restrictions for special one-qudit gates; Theorem 1.3 cannot simply be quoted with its $U(d)$ assumption removed.

For local rotations $e^{-itX}$ and $e^{-itY}$, Euler angles are rescaled by the convention that these exponentials have angle $2t$ on the Bloch sphere. They generate each $SU(2)$ element by three rotations. The inference is about ideal real parameters. Their computation, finite precision, physical implementation and errors require separate contracts.

The fixed controlled-S identity used to extract a local phase already appears in [Garion–Cross, equation (12)](garioncross2020cnotdihedral.md). Its application to the constrained physical pulses and the five-mode endpoint code is in [Static compatibility fibers §62](../../docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md#62-五模式交互系数与保码端点控制). Existing native compilers with a larger phase-addressable menu are described in the [Numata–Yamanouchi control note](../QuantumChannels/numatayamanouchi2022nativecontrol.md); their control permissions must not be substituted for the fixed-phase menu used there.

## Static composition retains coherent information

For a finite circuit $U=U_L\cdots U_1$ on fixed finite-dimensional ports, inserting a complete orthonormal basis between adjacent factors gives

$$
\langle x_L|U|x_0\rangle
=\sum_{x_1,\ldots,x_{L-1}}
\prod_{t=1}^{L}\langle x_t|U_t|x_{t-1}\rangle.
$$

This is ordinary matrix multiplication written as a static tensor contraction. The ports, order and complex amplitudes remain part of the description. A list of local configuration probabilities is insufficient: $(|000\rangle+|101\rangle)/\sqrt2$ and $(|000\rangle-|101\rangle)/\sqrt2$ are orthogonal but have identical occupancy probabilities and means. Squaring individual amplitudes before contraction loses the interference between paths. The identity gives neither a cheap general contraction algorithm nor an identification of a configuration polytope with physical spacetime.

All exposition here is citation-only; no article text, figures or downloaded source files are redistributed.
