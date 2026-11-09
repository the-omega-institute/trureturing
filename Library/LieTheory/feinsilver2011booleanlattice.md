---
bibkey: feinsilver2011booleanlattice
authors: Philip Feinsilver
year: 2011
title: "Representations of sl(2) in the Boolean lattice, and the Hamming and Johnson schemes"
doi: null
url: https://arxiv.org/abs/1102.0368v2
claim: "Boolean-lattice primitive strings give an orthogonal decomposition with the sl(2) ladder action, factorial norm formula, and choose(n,l)-choose(n,l-1) vacuum multiplicities."
strata_touched:
  - D5/S3/Quantum/SpinChains/BooleanCollectiveLadders
license: citation-only
triage: anchor
---

# Primitive strings in the Boolean sl(2) representation

Sections 2.2–2.2.3, printed pp. 3–5, identify the complex subset basis, its homogeneous layers, the add-element operator T and its adjoint T*. Section 3, printed pp. 8–9, describes a vacuum \(\phi_0\) with \(L\phi_0=0\) and principal number N. The generated string \(\phi_j=R^j\phi_0\), \(0\le j\le N\), obeys Eq. (8):

\[
R\phi_j=\phi_{j+1},\qquad
L\phi_j=j(N+1-j)\phi_{j-1},\qquad
H\phi_j=(N-2j)\phi_j.
\]

The end of printed p. 9 states \(R^{N+1}\phi_0=0\). Section 3.1, printed p. 10, gives orthogonality and

\[
\lVert\phi_j\rVert^2=j!\,N^{\underline j}\lVert\phi_0\rVert^2.
\]

Section 4.2, printed pp. 13–15, constructs the full Boolean decomposition and identifies the principal number at vacuum level ℓ as n−2ℓ, with the action restated in Eq. (16). Proposition 4.3, printed p. 15, states that the number of vacua at level \(\ell\le n/2\) is \(\binom n\ell-\binom n{\ell-1}\). Section 4.2.2, printed p. 16, proves orthogonality across the generated strings and states that scaling the basis makes the transformation unitary. Section 3 allows every nonnegative principal number, including the one-dimensional spin-zero string.

For the collective Boolean ladders, the paper's site count n is 2S, its vacuum level ℓ is t, its principal number N is 2S−2t, and its R and L are the collective U and L. Its diagonal H, also called U in the Boolean-lattice discussion, is −2 times the centered occupancy Z; it must not be confused with the collective raising map. The subset represented by a bit configuration x is \(\{i:x_i=0\}\). The source's negative-lower-index binomial convention corresponds to previousChoose(n,0)=0. Primitive vectors are the kernel of the lowering map inside a homogeneous layer. The literature formulas are independent of the choice of orthonormal primitive basis. The source starts with positive site count; the empty-site case is the direct one-dimensional extension with zero collective operators.

## Verified locator

- URL: https://arxiv.org/abs/1102.0368v2.
- PDF: https://arxiv.org/pdf/1102.0368v2; §§2.2–2.2.3, printed pp. 3–5; §3, printed pp. 8–9, Eq. (8) and the terminal-zero statement; §3.1, printed p. 10, the norm formula preceding Eq. (10); §4.2, printed pp. 13–15, Eq. (16); §4.2.1, Proposition 4.3, printed p. 15; §4.2.2, printed p. 16.

These locators refer to the arXiv v2 PDF. No comparison with a journal version is asserted.
