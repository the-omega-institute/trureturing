---
bibkey: tran2026puritymaxima
authors: Anh T. Tran
year: 2026
title: "Purity maxima, absolute separability, and spectral volumes of absolutely PPT states"
doi: 10.48550/arXiv.2611.01492
url: https://arxiv.org/abs/2611.01492v1
claim: "Theorem A determines the unique central APPT purity maximizer for n >= 2m^2-4 when m is even and n >= 2m^2-m-4 when m is odd, with n >= m >= 3. Theorem B gives full-rank APPT counterexamples to Ahiable–Kothakonda–Winter Conjecture 6.7 for every m >= 10 at n = 4m-2 and n = 4m. Theorem C proves the absolute-separability sufficiency of the linear inner-polytope criterion. Section 8 leaves the remaining lower-dimensional maxima and least eventual central threshold open in this source."
strata_touched:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QutritQuditMaximumPurity
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity
  - D5/S3/Quantum/Entanglement/AbsoluteSeparability/AhiableKothakondaWinterEq31
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2611.01492

Source: https://arxiv.org/abs/2611.01492v1

Preprint v1, submitted 2026-11-01. The statements below are the preprint's
assertions, checked against its official arXiv source text. This independent
source verification is not an independent proof check or Lean/kernel
acceptance of those assertions.

## Theorem A: eventual central maximum

Theorem A, equations (1.2)–(1.4), assumes integers $n\ge m\ge3$ and
$$
n\ge
\begin{cases}
2m^2-4,&m\text{ even},\\
2m^2-m-4,&m\text{ odd}.
\end{cases}
$$
Put $d=mn$, $i_\star=\lceil(m-1)n/2\rceil$,
$D_\star=(m-1)d+2i_\star$, and $N=(m^2-1)n$. The exact APPT maximum
asserted there is
$$
P^{\mathrm{cen}}_{m,n}
=\frac{(m-1)^2d+4mi_\star}{D_\star^2}
=\begin{cases}
\dfrac{m}{N},&(m-1)n\text{ even},\\[1ex]
\dfrac{m(N+2)}{(N+1)^2},&(m-1)n\text{ odd}.
\end{cases}
$$
Its unique maximizing ordered spectrum is
$$
\lambda^{\mathrm{cen}}_{m,n}
=\frac{\bigl((m+1)^{[i_\star]},(m-1)^{[d-i_\star]}\bigr)}{D_\star},
$$
where $x^{[q]}$ denotes $q$ repeated entries. The maximizing states are
precisely the unitary conjugates of a diagonal state with this spectrum.

## Theorem B: counterexamples to Conjecture 6.7

Theorem B refutes the unrestricted conjecture recorded in
[Ahiable–Kothakonda–Winter](../ahiablekothakondawinter2026geometry.md), restated
as Conjecture 1.1 in this preprint. For every integer $m\ge10$ and each
$n\in\{4m-2,4m\}$, it gives an explicit full-rank APPT boundary spectrum
whose purity strictly exceeds the inner-polytope maximum
$$
\max\left\{\frac{mn+8}{(mn+2)^2},P^{\mathrm{cen}}_{m,n}\right\}.
$$
These are counterexamples under the literal APPT condition, not merely
spectra satisfying scalar necessary inequalities. Every scalar head–tail
inequality is strict at these spectra.

The exact proof locators are Lemma 4.1 (the finite matrix APPT criterion
for three distinct positive eigenvalues under its multiplicity assumptions),
Corollary 4.2 (the two scalar conditions when the largest eigenvalue is
simple), Proposition 4.3 (the full-rank APPT boundary family), and Theorem B
with its proof in Section 4.3 (the strict purity comparisons in both branches).
The latter uses
$$
(A_m,B_m,C_m)=(17m+92,7m+42,7m+28),\qquad h_m=2m^2-4m,
$$
$$
S_{m,n}=A_m+(h_m-1)B_m+(mn-h_m)C_m,\qquad
\lambda_{m,n}=\frac{(A_m,B_m^{[h_m-1]},C_m^{[mn-h_m]})}{S_{m,n}}.
$$
At $n=4m-2$ the exceeded inner-polytope maximum is
$(4m^2-2m+8)/(4m^2-2m+2)^2$; at $n=4m$ it is $1/(4(m^2-1))$.
These assertions do not turn an independently found similar spectrum into
a new resolution of the conjecture.

## Theorem C and remaining questions

Theorem C, proved in Section 6.1, assumes $2\le m\le n$ and a state with
ordered eigenvalues $\lambda_1\ge\cdots\ge\lambda_d\ge0$, $d=mn$.
It asserts that
$$
\sum_{j=1}^{m-1}\lambda_j
\le 2\lambda_d+\sum_{j=1}^{m-1}\lambda_{d-j}
$$
implies absolute separability. This is the linear criterion of
Ahiable–Kothakonda–Winter equation (31), answering their Section 7 question.
It supplies a literature result without changing the origin or acceptance
status of existing project proofs.

Section 8 leaves open, for $m\ge4$, the remaining exact APPT purity maxima
below Theorem A's dimension bounds, and the least integer $n_0$ such that
the central spectrum is the unique APPT purity maximizer for every
$n\ge n_0$. Theorem A bounds $n_0$ from above; Theorem B's spectra give
lower bounds on the maxima and need not be global maximizers. This is the
open boundary stated in this source, not a guarantee of worldwide novelty
or a replacement for a current literature search.
