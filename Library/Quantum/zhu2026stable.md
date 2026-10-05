---
bibkey: zhu2026stable
authors: Xiuwu Zhu; Yu Wang
year: 2026
title: Uniformly Stable Minimal Weyl–Heisenberg Measurements Approaching the SIC Benchmark
doi: null
url: https://arxiv.org/abs/2608.11850v1
claim: The paper states uniform finite-field Weyl–Heisenberg stability in characteristic three as open; its flat-plus-spike state supplies the construction analyzed here at phase zero.
strata_touched:
  - D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity
license: citation-only
triage: anchor
---

# Characteristic-three flat-plus-spike ambiguity

The source is arXiv:2608.11850v1, Xiuwu Zhu and Yu Wang. Section IV.1,
equations (62), (68), and (69), gives the flat-plus-spike state and its
ambiguity calculation in characteristic two. Section IV.2 and Section VI
state the characteristic-three uniform-stability question as open. Appendix F,
equations (147)–(150), specifies finite-field labels and the spectral interface.
These locators refer to the downloaded arXiv HTML source, not the section
numbering quoted in GitHub issue #13556.

For a finite field K of cardinality q, set s = sqrt(q) and

\[
\phi(x)=\frac{1+s\,\mathbf1_{x=0}}{\sqrt{2q+2s}}
         =\frac{q^{-1/2}+\mathbf1_{x=0}}{\sqrt{2+2q^{-1/2}}}.
\]

This is equation (62) at phase zero, analyzed over characteristic three rather
than the paper's characteristic-two domain. For any nontrivial complex additive
character ψ, use the same operator word D(a,b) = X_a Z_b, acting on coordinates by
D(a,b)f(x) = ψ(b(x−a)) f(x−a). The Lean module proves normalization and

\[
A(a,b)=\langle\phi,D(a,b)\phi\rangle
 =\frac{q\mathbf1_{b=0}+q\mathbf1_{a=0}+s(1+\psi(-ba))}{2q+2s}.
\]

The character sum is evaluated with pinned Mathlib's
`AddChar.sum_mulShift` and `AddChar.IsPrimitive.of_ne_one`. In characteristic
three, ψ(x)^3 = 1. Factoring z^3−1 shows that either z=1 or
1+z=−z^2; unit modulus then gives |1+z|^2 at least one. The resulting
nonidentity bounds, proved for every finite characteristic-three field and
every nontrivial ψ, are

\[
|A(a,b)|^2\ge\frac1{4(\sqrt q+1)^2},\qquad
(q+1)|A(a,b)|^2\ge\frac18\quad((a,b)\ne(0,0)).
\]

The second bound uses (sqrt(q)−1)^2 ≥ 0. In particular, it does not use the
incorrect comparison with 1/7 in issue #13556: at q=3 the proposed expression
(q+1)/(4(sqrt(q)+1)^2) is approximately 0.133975, below 1/7.

## Exact remaining boundary

In the target family, ψ is the canonical character
exp(2πi Tr_(F_(3^r)/F_3)(x)/3), with the F_3 trace represented by an integer
modulo three. For g=(a,b), Π_g=D(a,b)|φ⟩⟨φ|D(a,b)^† and
G^Π[u,v]=Tr(Π_u Π_v); the indices u,v,g range over F_(3^r)^2.
The original target remains

\[
\exists c>0\;\forall r\in\mathbb N,\ r\ge1\;\exists\phi_r\in
\mathbb C^{\mathbb F_{3^r}},\quad
\sum_x|\phi_r(x)|^2=1,\quad
\forall w,\ \sum_g w(g)=0\Longrightarrow
\frac{c\,3^r}{3^r+1}\sum_g|w(g)|^2\le
\operatorname{Re}(w^*G^\Pi_{\phi_r}w).
\]

This module does not define the projectors or G^Π, prove finite-field Weyl
trace orthogonality, establish the Fourier/Parseval or synthesis identity for
that Gram matrix, or instantiate the canonical trace character on every
`GaloisField 3 r`. None of these is assumed as a premise. The proved ambiguity
bound would provide c=1/8 after a faithful Gram/Rayleigh bridge and the exact
family instantiation are proved. Informational completeness, minimal POVM
normalization, and an attained eigenvalue are also not claimed here.

The existing `WeylDisplacement`, `WeylDisplacementAdjoint`,
`WeylDisplacementConjugation`, and `WeylDisplacementTrace` modules concern
cyclic ZMod M labels. They were inspected for reuse, but their displacement
and orthogonality lemmas cannot be substituted for additive extension-field
labels when r>1. The present finite-field calculation reuses Mathlib character
orthogonality instead; it is not a cyclic result relabelled as a field family.

## Search and admission boundary

Repository D5/Blueprint/Library and pinned Mathlib v4.33.0 were searched for
Weyl–Heisenberg, additive-character ambiguity, and Weyl projector-Gram bounds.
The cyclic modules and upstream character APIs supply prerequisites, but no
exact characteristic-three spike-intensity theorem was found in the searched
scope. GitHub Lean code searches for Weyl–Heisenberg and ambiguity surfaced
unrelated fermion and metrology material, not this theorem. These checks do not
establish mathematical novelty or complete a current literature survey.

The bounds are repository-derived from the source construction, not theorems
attributed to Zhu–Wang in characteristic three. The live new inference is the
cubic-root noncancellation estimate applied to the explicitly computed overlap.
Private finite-sum and algebraic facts are consumed by the public proofs;
there are no unconsumed specializations of existing theorems. The module's
`utility: none` means general mathematical proofs rather than a numerical
reduction, bounded enumeration, checker, or certified finite instance.
