---
bibkey: srinivasan2010symmetricchains
authors: Murali K. Srinivasan
year: 2010
title: "Symmetric chains, Gelfand-Tsetlin chains, and the Terwilliger algebra of the binary Hamming scheme"
doi: null
url: https://arxiv.org/abs/1001.0280v2
claim: "The complex Boolean lattice has an orthogonal symmetric Jordan basis; normalized raising coefficients are square roots of (u+1-k)(n-k-u), and chains starting at rank k have multiplicity choose(n,k)-choose(n,k-1)."
strata_touched:
  - D5/S3/Quantum/SpinChains/BooleanCollectiveLadders
license: citation-only
triage: anchor
---

# Orthogonal symmetric chains in the Boolean lattice

The complex vector space has the subsets of an n-element set as an orthonormal basis. The up operator adds one element, the down operator removes one element, and homogeneous rank is subset cardinality.

Theorem 1.2, printed p. 3, states orthogonality of the symmetric Jordan basis and the successive norm ratio

\[
\frac{\lVert x_{u+1}\rVert}{\lVert x_u\rVert}
=\sqrt{(u+1-k)(n-k-u)},\qquad k\le u<n-k.
\]

Equations (3)–(4), printed p. 4, give the unnormalized ladder action and centered weights. Equation (5) and its adjoint discussion, printed p. 5, give the normalized raising and lowering actions. In §2, printed p. 8, the paragraph defining \(p_k=n-2k+1\) and \(q_k=\binom nk-\binom n{k-1}\) states that there are \(q_k\) chains starting at rank k; the matrix whose columns are the normalized chain vectors is unitary.

For the Boolean collective ladder notation, n=2S, the starting rank is k=t, the ascending chain position is q=u−t, and the spin is S−t. Thus the coefficient is \(\sqrt{(q+1)(2S-2t-q)}\). The native coordinate r=2(S−t)−q reverses this ascending order. The paper supplies the classical chain decomposition and coefficients, not the identifiers or matrix adapters of the Lean implementation. The positive-n formulation extends at n=0 by the single empty subset and zero up/down operators.

## Verified locator

- URL: https://arxiv.org/abs/1001.0280v2.
- PDF: https://arxiv.org/pdf/1001.0280v2; Theorem 1.2 and Eqs. (1)–(2), printed p. 3; Eqs. (3)–(4), printed p. 4; Eq. (5) and the adjoint discussion, printed p. 5; §2, printed p. 8, the definitions of p_k, q_k and the unitary matrix N(n).

These locators refer to the arXiv v2 PDF. No comparison with a journal version is asserted.
