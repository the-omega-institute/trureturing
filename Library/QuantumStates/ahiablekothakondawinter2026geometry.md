---
bibkey: ahiablekothakondawinter2026geometry
authors: Jennifer Ahiable; Naga Bhavya Teja Kothakonda; Andreas Winter
year: 2026
title: "The geometry of absolute separability and other convex matrix properties from spectrum"
doi: 10.48550/arXiv.2608.03390
url: https://arxiv.org/abs/2608.03390v2
claim: "Conjecture 6.7 states equality of APPT maximum purity and the inscribed polytope maximum, with the spectra of equation (44). Theorem 6.2 proves that the linear condition (31) implies absolute PPT; Section 7 asks to show that (31) is sufficient for absolute separability."
strata_touched:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QutritQuditMaximumPurity
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitQuintitMaximumPurity
  - D5/S3/Quantum/Entanglement/AbsoluteSeparability/AhiableKothakondaWinterEq31
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2608.03390

Source: https://arxiv.org/abs/2608.03390v2

## Conjecture 6.7

Page 29, verbatim statement (equation reference rendered as its printed number):

Let $\mathcal P_{m,n}\subseteq \mathrm{APPT}_{m,n}$ be the inscribed absolute PPT polytope with $2\leq m\leq n,\; n>2$. Then
$$
      \max_{\lambda\in \mathrm{APPT}_{m,n}}
    \sum_{i=1}^{mn}\lambda_i^2=  \max_{\lambda\in\mathcal P_{m,n}}
    \sum_{i=1}^{mn}\lambda_i^2
$$
and occurs at the spectra given by Eq. (44).

## Inscribed-polytope maximum

Corollary 6.4, pages 26–27, verbatim source statement:

Let $\mathcal P_{m,n}\subseteq \mathrm{APPT}_{m,n}$ be the inscribed absolute PPT polytope with $2\leq m\leq n,\; n>2$. The maximum achievable purity of a quantum state $\rho \in \mathcal{M}_m \otimes \mathcal{M}_n$ with spectrum $\lambda \in \mathcal P_{m,n}$ is given by
$$
    \max_{\lambda\in\mathcal P_{m,n}}
    \sum_{i=1}^{mn}\lambda_i^2=
    \begin{cases}
    \displaystyle
    \frac{mn+8}{(mn+2)^2},&\textrm{if }  n<n^*, \\[2ex]
    \displaystyle
    \frac{m}{(m^2-1)n},&\quad n\geq n^* \text{ and } \big(m \text{ is odd or } n \text{ is even}\big), \\[2ex]
    \displaystyle
    \frac{mn(m^2-1)+2m}{
    \big((m^2-1)n+1\big)^2},
    &\quad n\geq n^*,\ m \text{ is even and } n \text{ is odd }
    \end{cases}$$ where $$n^* = \frac{2(m^2-2) + 2\sqrt{(m^2-1)(m^2-4)}}{m}.$$
Furthermore, the spectrum of the maximal purity state with $\lambda_1 \geq\cdots\geq \lambda_{mn}\geq 0$ is given by
$$
    \begin{cases}
      \lambda_1 =\frac{3}{mn+2} , \quad \lambda_j = \frac{1}{mn+2} &\text{for } j = 2,\ldots, mn,\  \qquad \qquad \qquad \qquad \quad \;\text{ if } n < n^* \\
      \lambda_i =a , \quad \lambda_j =b &\text{for } i = 1,\ldots, t \ \text{ and } \ j = t + 1, \ldots, mn, \ \text{ if } n \geq n^*
    \end{cases}
$$
where the block size $t = \left\lceil \frac{(m-1)n}{2} \right\rceil$, and the eigenvalues $a$ and $b$ evaluate exactly to
$$
    a = \frac{m+1}{2t + mn(m-1)} \quad \text{and} \quad b = \frac{m-1}{2t + mn(m-1)}.
$$

## Theorem 6.2 and the Section 7 question

Theorem 6.2, page 23, verbatim:

> Given a mixed state $\rho \in \mathcal M_m \otimes \mathcal M_n$ with a decreasingly ordered eigenvalue spectrum $\lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_{mn}\geq 0$, if the following linear inequality holds:
> $$2\lambda_{mn} + \sum_{k=1}^{m-1} \lambda_{mn-k} \ge \sum_{k=1}^{m-1} \lambda_k \qquad (31)$$
> then the spectrum lies within $\mathcal{P}_{m,n}$, and $\rho$ is absolutely PPT.

Section 7 (Conclusion), page 39:

> Thus, another matter of interest is to resolve Conjecture 6.7 in the positive, and to show that the linear condition in Eq. (31) is sufficient for absolute separability: because then the maximum purity over all three sets must coincide.

## Absolute separability convention

Page 2:

> Within this class of states lies a convex and compact subset of separable states that remain separable after the transformation $U\rho U^\dagger$ under all global unitaries $U$ in the unitary group $\mathcal{U}(mn)$, widely referred to as absolutely separable states.

## Partial transpose convention

Page 2:

> $\Gamma(X \otimes Y) = X \otimes Y^T$, where $X \in \mathcal M_m$ and $Y \in \mathcal M_n$, and $T$ denotes the standard matrix transpose.

## Absolute PPT convention

Page 2:

> Defined analogously to absolutely separable states, absolute PPT states are those states which remain PPT after global unitary rotations and have been completely characterized across all dimensions [17].

Page 11:

> Suppose $\lambda$ is the spectrum of a bipartite state. Then $\lambda\in \mathrm{APPT}_{m,n}$ if and only if for all unitaries $U\in \mathcal{U}(mn)$, $(U\diag(\lambda)U^\dagger)^\Gamma \geq 0$.

The matrix encoding uses the second-factor partial transpose on `Fin 3 × Fin n`. Its trace-squared purity is the real part of `Matrix.trace (rho * rho)`. The qutrit sector substitutes m = 3 and t = n in Corollary 6.4. The two candidate purities become (3n + 8)/(3n + 2)^2 and 3/(8n).


## Four-row correspondence and scope

Theorem 6.3 computes the exact optimum **inside** the inscribed polytope
$\mathcal P_{m,n}$; Corollary 6.4 gives its branch and parity formulas.
Since this polytope is contained in APPT, its optimum and listed attaining
spectra supply an APPT lower bound. The unrestricted APPT upper bound is
the additional assertion of Conjecture 6.7. The formulas and attainers
quoted above must not be attributed to a later proof of that upper bound.

For $m=4$, put
$$
 t=\left\lceil\frac{3n}{2}\right\rceil
   =\left\lfloor\frac{12n+4}{8}\right\rfloor,
 \qquad D=12n+2t.
$$
On the two-level branch, the published spectrum is
$$
 \frac{(5^t,3^{4n-t})}{D},
 \qquad F(n)=\frac{36n+16t}{D^2}
 =\begin{cases}
    \dfrac{4}{15n},& n\text{ even},\\[1ex]
    \dfrac{60n+8}{(15n+1)^2},& n\text{ odd}.
   \end{cases}
$$
Here the superscripts in the spectrum denote multiplicities. A coordinate
projector $P$ of rank $t$ realizes it as $\rho_*=(3I+2P)/D$.
The printed transition specializes to
$n^*=7+3\sqrt5\in(13,14)$, so this is the published inner-polytope branch
for every integer $n\ge14$. The rank-one branch, its attaining spectrum,
and the transition are also published prior work.

At $n=13$, the published rank-one vertex of Eq. (47) is
$\rho_{13}=(I+2|00\rangle\langle00|)/54$, with spectrum
$(3,1^{51})/54$. Its actual APPT purity is $5/243$, whereas the two-level
formula gives $F(13)=197/9604$, and
$$
 \frac5{243}-\frac{197}{9604}=\frac{149}{2333772}>0.
$$
This witness rules out an eventual threshold at or below 13 for the
assertion that $F(n)$ is the APPT maximum at every later dimension. It
does not determine the APPT maximum at 13 or in any other dimension
7 through 13. The witness mechanism and this inner-polytope comparison
come from the paper, rather than a new lower-bound construction.

The existing four-row consumers listed in `strata_touched` relate the
literal complex-density APPT problem to this conjecture. The
`QuadbitQuintitMaximumPurity` owner also explains the complete varying-$n$
application: one sorted spectrum retains its actual APPT labelled
diagonal, the genuine product corners give its literal K1 and rank-four
necessary inequality, and `actual_k1_l4_purity_bound` applies at
$N=4n\ge56$. The coordinate-projector density gives actual attainment,
so together these yield the real attained supremum and the two parity
formulas for $n\ge14$, with least eventual onset 14. The scalar theorem
with premise $N\ge56$ is not used at $N=52$ for the witness.

A prior formal result,
`APPTReview.appt_rectangular_maximum_formula` in
[mxym/math at commit 479acd5d6269faf94433ad6b694c5b7979027c69](https://github.com/mxym/math/blob/479acd5d6269faf94433ad6b694c5b7979027c69/formalizations/appt-high-dimensional-review/APPTReview/RectangularMaximum.lean#L78),
already states the rounded physical maximum for $m\ge3$ and
$n\ge m^3-m-2$, hence for $m=4,n\ge58$. The candidate additional result
is the universal APPT upper bound in $14\le n\le57$. The paper already
supplies the inner-polytope formulas, listed attainers and transition;
none is a new priority claim here, and no external code is transplanted.

The historical $n\ge17$ application has compilation and accepted scoped
axiom-closure evidence. Official CI has now compiled the complete
$n\ge14$ physical application and its suppliers, and the scalar
$N\ge56$ result has a separate selected successful build. The current
full axiom/report closure, supplier registration evidence and final
official acceptance remain pending; the present Scribe/Reg/Library
source updates are uncompiled. The primary-source comparison used here
is confined to v2 and is not an exhaustive later-literature or uniqueness
check. No final unique completion, general-$m$ resolution, classification
of all maximizers, equality of APPT with absolute separability, or
maximum in dimensions 7 through 13 is asserted by this update.

## Later literature

### Tran: purity maxima, absolute separability, and spectral volumes

Anh T. Tran, *Purity maxima, absolute separability, and spectral volumes of
absolutely PPT states* (2026), citation key `tran2026puritymaxima`.

DOI: https://doi.org/10.48550/arXiv.2611.01492

Source: https://arxiv.org/abs/2611.01492v1

Preprint v1, submitted 2026-11-01. The statements below are the preprint's
assertions, checked against its official arXiv source text. This independent
source verification is not an independent proof check or Lean/kernel
acceptance of those assertions.

#### Theorem A: eventual central maximum

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

#### Theorem B: counterexamples to Conjecture 6.7

Theorem B refutes the unrestricted Ahiable–Kothakonda–Winter
[Conjecture 6.7 quoted above](#conjecture-67), restated as Conjecture 1.1
in Tran’s preprint. For every integer $m\ge10$ and each
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

#### Theorem C and remaining questions

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
