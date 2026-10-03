---
bibkey: kerenidis2026scalablequantumml
authors: Iordanis Kerenidis
year: 2026
title: "Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency"
doi: 10.48550/arXiv.2607.24014
url: https://arxiv.org/abs/2607.24014v2
claim: "Conjecture 20: the unitary butterfly at uniformly random parameters is a relative-error two-design in the second exterior representation, with error O(1/n) in completely positive order."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/ButterflyLambdaTwoRelativeDesignRefutation
license: citation-only
triage: anchor
---

# The butterfly relative-error exterior-square design conjecture

## Verified locator

Iordanis Kerenidis, *Scalable Quantum Machine Learning: Trainability,
Expressivity and Efficiency*, arXiv:2607.24014v2 [quant-ph], version 2
(20 August 2026). DOI: https://doi.org/10.48550/arXiv.2607.24014.
Source: https://arxiv.org/abs/2607.24014v2.

## Statement

Conjecture 20, PDF p. 16, is the following verbatim TeX quotation from
`quantum_v2.tex`, `\label{conj:lambda2_design}` in
`\label{sec:butterfly_circuit}`:

> The unitary butterfly W<sub>n</sub> at uniformly random parameters is an ε-approximate unitary 2-design on U(n) in the antisymmetric 2-particle representation Λ² ℂ<sup>n</sup>, in the *relative* (multiplicative) sense, with ε = O(1/n): writing Φ₂<sup>Λ²,W<sub>n</sub></sup>[Y] := E<sub>W<sub>n</sub></sub>[Λ²(W<sub>n</sub>)<sup>⊗ 2</sup> Y Λ²(W<sub>n</sub>)<sup>†⊗ 2</sup>], for Y ∈ End(Λ²ℂ<sup>n</sup> ⊗ Λ²ℂ<sup>n</sup>), and Φ₂<sup>Λ²,Haar</sup> for the corresponding Haar second moment, (1−ε) Φ₂<sup>Λ²,Haar</sup> ⪯ Φ₂<sup>Λ²,W<sub>n</sub></sup> ⪯ (1+ε) Φ₂<sup>Λ²,Haar</sup> as completely positive maps. In particular Φ₂<sup>Λ²,W<sub>n</sub></sup> has fixed-point space of dimension 3, matching the Haar decomposition Λ² ⊗ Λ² = V<sub>(2,2)</sub> ⊕ V<sub>(2,1,1)</sub> ⊕ V<sub>(1,1,1,1)</sub> into three irreducible U(n)-representations.

```tex
\begin{conjecture}[Butterfly is a relative-error $2$-design on $\Lambda^2$]
\label{conj:lambda2_design}
The unitary butterfly $W_n$ at uniformly random parameters is an
$\varepsilon$-approximate unitary $2$-design on $U(n)$ in the antisymmetric
$2$-particle representation $\Lambda^2 \mathbb{C}^n$, in the \emph{relative}
(multiplicative) sense, with $\varepsilon = O(1/n)$: writing
\begin{equation}\label{eq:lambda2-secondmoment}
\Phi_2^{\Lambda^2,W_n}[Y] := \mathbb{E}_{W_n}\!\left[\Lambda^2(W_n)^{\otimes 2}\,
Y\, \Lambda^2(W_n)^{\dagger\otimes 2}\right],
\end{equation}
for $Y \in \mathrm{End}(\Lambda^2\mathbb{C}^n \otimes \Lambda^2\mathbb{C}^n)$,
and $\Phi_2^{\Lambda^2,\mathrm{Haar}}$ for the corresponding Haar second
moment,
\begin{equation}
\label{eq:relative_design}
  (1-\varepsilon)\,\Phi_2^{\Lambda^2,\mathrm{Haar}}
  \;\preceq\; \Phi_2^{\Lambda^2,W_n}
  \;\preceq\; (1+\varepsilon)\,\Phi_2^{\Lambda^2,\mathrm{Haar}}
\end{equation}
as completely positive maps. In particular $\Phi_2^{\Lambda^2,W_n}$ has
fixed-point space of dimension $3$, matching the Haar decomposition
$\Lambda^2 \otimes \Lambda^2 = V_{(2,2)} \oplus V_{(2,1,1)} \oplus
V_{(1,1,1,1)}$ into three irreducible $U(n)$-representations.
\end{conjecture}
```

The literal circuit definition, PDF p. 10, section
`\label{sec:butterfly_circuit}`, is:

```tex
An $n$-qubit unitary butterfly circuit of depth $K = \log_2 n$ consists of $K$
layers. Layer $\ell \in \{1,\ldots,K\}$ applies a full-width layer of $n$
single-qubit phase gates followed by RBS gates on each of the $n/2$ disjoint
pairs with stride $2^{\ell-1}$:
\begin{align}
  U(\btheta,\bphi) &= U^{(K)}\cdots U^{(1)}, \\
  U^{(\ell)} &= \Bigl[\bigotimes_{j=1}^{n/2}
  \mathrm{RBS}(\theta_\ell^{(j)})\Bigr] \cdot
  \bigotimes_{i=1}^{n} R_z(\phi_\ell^{(i)}).
\end{align}
Equivalently, each pair carries the three-parameter primitive $\calG$ of
Eq.~\eqref{eq:gate_primitive}, one $R_z$ on each of its two qubits.
The $R_z$ gate acts as $R_z(\phi)\ket{0} = e^{i\phi/2}\ket{0}$,
$R_z(\phi)\ket{1} = e^{-i\phi/2}\ket{1}$: a diagonal one-body unitary, hence
passive FLO and particle-number preserving. Within each layer, all $n/2$ gate
pairs act on disjoint qubits, so generators from different pairs commute---the
key structure exploited by the multi-layer parallel parameter-shift rule.
```

The circuit consists of layers in increasing stride order, with matrix
product `U^(K) ... U^(1)`. Layer ell applies a full-width phase layer,
then disjoint RBS gates at stride `2^(ell-1)`. The one-excitation RBS
matrix is `[[cos(theta), sin(theta)], [-sin(theta), cos(theta)]]`.
The literal phase convention is `R_z(phi)|0> = exp(i phi/2)|0>` and
`R_z(phi)|1> = exp(-i phi/2)|1>`; the one-particle phase at mode j is
`exp(i (sum_i phi_i/2 - phi_j))`, including the common vacuum phase.

The encoding uses `Fin K -> Fin 2`, with bit zero of stride one,
identified with `Fin (2^K)` by `finFunctionFinEquiv`. There is one angle
for every layer/pair and one phase for every layer/mode, all independently
uniform on `[0,2*pi)`. Exterior-square coordinates are the two-by-two
minors in the ordered basis `e_i wedge e_j`, `i<j`. Completely positive
order uses Mathlib's bundled maps and their finite matrix amplifications.
The asymptotic statement is read as one constant c and one threshold N0,
followed by every power-of-two n above N0 and an error `0 <= epsilon <= c/n`.

Theorem 19 (`\label{thm:sharp_rate}`, pp. 16–17) assumes this
conjecture for the literal butterfly. Theorem 16's additive-error statement
uses one copy of the exterior representation. The independent-halves
ensemble of Theorem 13 (`\label{thm:interior_halves}`) is a different
ensemble. The refutation concerns the displayed relative two-copy bound;
it makes no assertion about those other statements.
