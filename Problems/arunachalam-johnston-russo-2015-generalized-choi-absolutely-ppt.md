---
slug: arunachalam-johnston-russo-2015-generalized-choi-absolutely-ppt
bibkey: arunachalam2015absolute
doi: null
url: https://arxiv.org/abs/1405.5853v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.result
---

# No generalized Choi map detects absolutely PPT entanglement

## Problem

S. Arunachalam, N. Johnston and V. Russo, *Is absolute separability determined by the partial
transpose?*, Quantum Inf. Comput. 15(7–8), 694–720 (2015); arXiv:1405.5853v3. Section 7 (p. 21):

> Other open problems in this work include proving that all of the generalized Choi maps
> $\Phi_{b,c}$ in Section 5.3 are incapable of detecting absolutely PPT entanglement (including
> those in the light gray region of Figure 3) …

Here $\Phi_{b,c}(X)=\tfrac12\begin{pmatrix}ax_{11}+bx_{22}+cx_{33}&-x_{12}&-x_{13}\\-x_{21}&cx_{11}+ax_{22}+bx_{33}&-x_{23}\\-x_{31}&-x_{32}&bx_{11}+cx_{22}+ax_{33}\end{pmatrix}$
with $a=2-b-c$, positive but not completely positive exactly when $(b,c)\ne(0,0)$, $b,c\ge0$ and
$b+c\le1$ or $bc\ge(b+c-1)^2$ (Section 5.3, p. 14). The verbatim texts are in
[the literature note](../Library/QuantumChannels/arunachalam2015absolute.md).
Issue [#14738](https://github.com/the-omega-institute/trureturing/issues/14738) preregisters the
reading and the proof plan.

## Motivation

The absolute separability problem asks for a spectral characterization of states that stay
separable under every global unitary. The source asks whether absolutely PPT states, those whose
every unitary conjugate has positive partial transpose, are absolutely separable, and tests this
against the positive maps most likely to detect PPT entanglement. The generalized Choi maps contain
the Choi map, the reduction map and indecomposable exposed maps.

## Gap

The source's Theorem 3 proves non-detection on a dark subregion of the parameter set from
eigenvalue bounds on $(id\otimes\Phi_{b,c}^\dagger)(|v\rangle\langle v|)$; for the light region it has
only numerical evidence. The literature check in #14738 found no proof for the whole family;
`not-found-in-searched-scope`.

## Route

For a unit vector $v$, $\langle v,(id\otimes\Phi_{b,c})(\rho)v\rangle=\operatorname{tr}(\rho W_v)$ with
$W_v=(id\otimes\Phi_{b,c}^\dagger)(|v\rangle\langle v|)$ and $\operatorname{tr}W_v=1$.

1. *Witness purity.* With $v=\sum_jx_j\otimes e_j$, $p_j=\lVert x_j\rVert^2$, $S=\sum_jp_j^2\ge1/3$, $\sigma$
   the Gram matrix of the $x_j$, $r=\operatorname{tr}\sigma^2\le1$ and $q=a^2+b^2+c^2$,
   $\tfrac12-\operatorname{tr}W_v^2=\tfrac{(4-q)(1-r)}8+\tfrac{(2-q)(3S-1)}8$, so $\operatorname{tr}W_v^2\le\tfrac12$
   when $q\le2$. On the curved part of the region $q-2=2[(b+c-1)^2-bc]\le0$.
2. *State purity.* The repository's frozen `QutritN3PurityBound.purity_bound` gives
   $\operatorname{tr}\rho^2\le17/121$ for every absolutely PPT state on $\mathbb C^3\otimes\mathbb C^3$.
3. *Cauchy–Schwarz.* $\operatorname{tr}(\rho W_v)=\tfrac19+\operatorname{tr}((\rho-\tfrac I9)(W_v-\tfrac I9))
   \ge\tfrac19-\sqrt{\tfrac7{18}\cdot\tfrac{32}{1089}}>0$, since $(\tfrac19)^2-\tfrac7{18}\cdot\tfrac{32}{1089}=\tfrac1{1089}$.
4. *Triangle.* For $b+c\le1$, $\Phi_{b,c}=(1-b-c)\Phi_{0,0}+b\Phi_{1,0}+c\Phi_{0,1}$, where
   $\Phi_{1,0},\Phi_{0,1}$ have $q=2$ and $\Phi_{0,0}(X)=\tfrac12\sum_DDXD$ with
   $D\in\{\operatorname{diag}(1,-1,0),\operatorname{diag}(0,1,-1),\operatorname{diag}(-1,0,1)\}$ is completely positive.

## Falsifier

An error in the witness-purity identity, in the hypotheses of the purity bound, or in the reading
of $\Phi_{b,c}$ or of absolute PPT. Positive controls in #14738: $\Phi_{1,1}$, $\Phi_{1,0}$ and
$\Phi_{0.5,1.2}$ detect the maximally entangled state, so the claim is not vacuous; the bound
$\operatorname{tr}W_v^2\le\tfrac12$ is attained.

## Evidence

`D5/S3/Quantum/Entanglement/AbsolutePPT/GeneralizedChoiNonDetection.lean` defines `choiGen`
($\Phi_{b,c}$ entry by entry), `idTensor` (the map on the second tensor factor, blockwise) and
`claim`, and proves the public `witness_purity_bound` and `result : claim` from the frozen
`purity_bound` and `APPT` of `D5/S3/Quantum/Entanglement/AbsolutePPT`. The axiom closure of
`result` is exactly `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry` or
`native_decide`.
The module statement is `sha256:a6a9d31ad0b16bdf4565d2f33d08939281a73a86eb48d0a01be8e3900feab930`; `result` is
`sha256:987b9c4a12f2a5f7df6278f4744be224d7385f30daf96dc78f658701fa097a25`, `claim` is
`sha256:ec3a7c9056ef82a79d549dbc7543bf3f3b795777261aca60d289a647a0bdf9f3` and `witness_purity_bound` is
`sha256:ea6338444a379797b6331ad8ffa059ab8a8bbcb96d7b2461aee7d4c37368cde2`. The Freeze event is
`sha256:0c500069bbf6c8fd9d667879a968f2163d59a6619ef81c80d80d0d432342a95e`.

## Triage

Tier 1: an open problem stated in a 2015 paper, preregistered in #14738 before any Lean.
`theorem`; resolution `proved`. Utility `none`; there is no digestion atom.

Every theorem of the module is bind-only by CLAUDE.md §3.2: unfolding of the new definitions with
`ring` normalization, instantiation of frozen and Mathlib lemmas, and `linarith`/`nlinarith`. Admission
basis `open-problem-resolution`; the new content is the settlement.

### What the proof shows

- **Proved by `result`:** for every $(b,c)$ for which $\Phi_{b,c}$ is positive and not completely
  positive, $(id_3\otimes\Phi_{b,c})(\rho)\ge0$ for every absolutely PPT $\rho\in M_3\otimes M_3$. No
  generalized Choi map, in particular neither the Choi map nor the reduction map nor the
  indecomposable exposed maps of the family, can certify that an absolutely PPT qutrit pair is
  entangled.
- **Mechanism (proved within the derivation):** the witness $W_v$ of every map with
  $a^2+b^2+c^2\le2$ has purity at most $1/2$, while an absolutely PPT state has purity at most
  $17/121$; two trace-one operators whose purities are this small cannot have a negative
  Hilbert–Schmidt inner product.
- **Derived, not formalized as a separate theorem:** the argument needs only
  $(\operatorname{tr}\rho^2-\tfrac19)(\tfrac12-\tfrac19)<\tfrac1{81}$, i.e. $\operatorname{tr}\rho^2<\tfrac17$, and
  $17/121<1/7$. Hence on $\mathbb C^3\otimes\mathbb C^3$ no positive map $\Phi$ such that every
  witness $(id\otimes\Phi^\dagger)(|v\rangle\langle v|)$ of a unit vector $v$ has trace one and purity at most
  $1/2$ detects the entanglement of any state of purity below $1/7$, absolutely PPT or not.
- **Open:** whether absolutely PPT states on $\mathbb C^3\otimes\mathbb C^3$ are absolutely separable
  (the source's main question), and the analogous statement for positive maps outside the
  generalized Choi family.

## ASSUMED-UNVERIFIED

The literature check in #14738 is bounded and does not establish worldwide novelty or priority.
