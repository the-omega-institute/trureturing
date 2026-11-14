---
bibkey: niestegge2015dynamical
authors: Gerd Niestegge
year: 2015
title: Dynamical Correspondence in a Generalized Quantum Theory
doi: 10.1007/s10701-015-9881-x
url: https://arxiv.org/abs/1402.0158v2
claim: Section 4 defines order derivations by positivity of all real exponentials, recalls their zero-evaluation characterization, and gives the anticommutator generators in operator algebras.
strata_touched: []
license: citation-only
triage: anchor
---

# Order derivations and anticommutator generators

The primary text is [arXiv:1402.0158v2](https://arxiv.org/html/1402.0158v2),
§4, “Order derivations”. A bounded real-linear operator $D$ is an order
derivation when $e^{tD}$ is positive for every real $t$. Applying the
condition also at $-t$ makes these exponentials order isomorphisms.
Lemma 3 recalls the equivalent vanishing condition: for every state
$\mu$ and every positive $x$, $\mu(x)=0$ implies $\mu(Dx)=0$.
The source credits Connes and the generalization by Evans and Hanche-Olsen.

In an operator algebra the source gives the selfadjoint order derivations
$X\mapsto(aX+Xa)/2$ and the skew order derivations
$X\mapsto i(bX-Xb)/2$, for selfadjoint $a,b$. Positivity of all
exponentials does not assert positivity of the generator itself.
The source's observable order unit is not the normalized predictive
center used in the application below.

The exact consumers are [the L3 continuation, Definition 93.1 and Theorem 93.3](../../docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_VI.md),
and its Proposition 94.2. The complex-cone witness takes $a=NP$,
so $D_P(X)=N(PX+XP)/2$ sends $I/N$ to $P$.
Its exponential is the explicit congruence
$X\mapsto e^{NtP/2}Xe^{NtP/2}$.
These are applications of the established terminology and example,
not new general order-derivation results.

The paper's separate dynamical-correspondence theorem is not used to
infer a Hamiltonian, a physical clock or a native gate sequence. In
particular a pure-directed order deformation of a predictive cone is
not identified with unit-preserving quantum time evolution.
