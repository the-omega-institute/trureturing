---
bibkey: vomende2025witnessoptimality
authors: Frederik vom Ende and Simon Cichy
year: 2025
title: "Simple Sufficient Criteria for Optimality of Entanglement Witnesses"
doi: null
url: https://arxiv.org/abs/2505.15615v2
claim: "Section IV asks whether the trace criterion of Corollary 2 (saturation of ⟨Ω|W|Ω⟩ ≥ −tr(W)/min{m,n} by a maximally entangled Ω) is equivalent to the kernel criterion of Theorem 2 (a vector of full Schmidt rank in the kernel of W + tr₂(W) ⊗ 1, or of W + 1 ⊗ tr₁(W))."
strata_touched:
  - D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2505.15615v2

Version 2 (27 June 2025; v1 21 May 2025), comments "submitted to Phys. Rev. A."; Crossref lists no
journal version (checked 2026-10-09). The quotations are from the v2 TeX source (`main.tex`); page
numbers refer to the v2 PDF. Witnesses and block positivity: Section II B, p. 3. Theorem 2: Section
III A, p. 8. Remark 3(i): p. 8. Corollary 2: p. 9. The question: Section IV, p. 12.

Witnesses (p. 3):

> Next, a convenient tool for detecting entanglement are entanglement witnesses. These are block-positive operators $W \in \mathbb C^{m\times m}\otimes\mathbb C^{n\times n}$ for which there exists $\sigma\geq 0$ such that ${\rm tr}(W\sigma)<0$; recall that $W$ is called block-positive if it satisfies $\langle x\otimes y | W |x\otimes y \rangle \geq 0$ for all $x,y$.

Theorem 2, the kernel criterion (p. 8):

> Given any witness $W\in\mathbb C^{m\times m}\otimes\mathbb C^{n\times n}$, the following statements hold. (i) If $m\leq n$ and if $\ker(W+{\rm tr}_2(W)\otimes{\bf1})$ contains a vector of Schmidt rank $m$, then $W$ is optimal. (ii) If $m\geq n$ and if $\ker(W+{\bf1}\otimes{\rm tr}_1(W))$ contains a vector of Schmidt rank $n$, then $W$ is optimal.

Remark 3(i) (p. 8) fixes the Schmidt rank of a vector as the rank of its coefficient matrix:

> … has the form $(0,a,b,-a,0,c,-b,-c,0)^T$ for some $a,b,c\in\mathbb C$, the Schmidt rank of which---by definition---is the rank of $\begin{pmatrix} 0&-a&-b\\a&0&-c\\b&c&0 \end{pmatrix}$.

Corollary 2, the trace criterion (p. 9):

> For all witnesses $W\in\mathbb C^{m\times m}\otimes\mathbb C^{n\times n}$ and all maximally entangled states $\Omega$---i.e., $\Omega$ has Schmidt rank $\min\{m,n\}$ and all its Schmidt coefficients equal $(\min\{m,n\})^{-1/2}$---it holds that $\langle\Omega|W|\Omega\rangle\geq-\,\frac{{\rm tr}(W)}{\min\{m,n\}}$. Moreover, if equality holds in (11) for some maximally entangled state $\Omega$, then $W$ is optimal.

Its proof writes $|\Omega\rangle=\sum_{j=1}^m\frac1{\sqrt m}|u_j\rangle\otimes|v_j\rangle$ with orthonormal
$\{u_j\}$, $\{v_j\}$ ($m\le n$) and derives the kernel criterion from equality, so the trace criterion
implies the kernel criterion.

The question (Section IV, p. 12):

> Next: is our trace-based criterion (Coro. 2) actually equivalent to our kernel criterion (Thm. 2)? This is the question mark in Fig. 2, and while the kernel criterion seems stronger we were not able to find a witness for which only the kernel criterion holds.

After the proof of Theorem 2 the source notes that the kernel criterion transfers to every
$(X\otimes{\bf1})W(X^\dagger\otimes{\bf1})$ with $X$ of full rank; its footnote to Corollary 2 notes
that for a kernel vector ${\rm vec}(X)$ of full Schmidt rank the trace in eq. (11) would have to be
replaced by a state-dependent quantity.
