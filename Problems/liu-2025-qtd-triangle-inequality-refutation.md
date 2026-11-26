---
slug: liu-2025-qtd-triangle-inequality-refutation
bibkey: liu2025quantumtriangular
doi: 10.48550/arXiv.2303.01952
url: https://arxiv.org/abs/2303.01952v5
triage: theorem
motivation_gids:
  - D5/S3/Divergence/QuantumTriangularMetricRefutation.result
---

# The square root of quantum triangular discrimination is not a metric

## Problem

Yupan Liu, *Complexity-theoretic perspectives on quantum state testing*, PhD thesis,
Nagoya University, January 2025, Open Problem 8.16, printed p. 180, asks:

> Is it possible to prove that the square root of quantum triangular discrimination, denoted as √QTD, is a distance metric? Specifically, for any quantum states ρ0, ρ1, and ρ2, can it be shown that the following inequality holds: √QTD(ρ0, ρ1) + √QTD(ρ1, ρ2) ≥ √QTD(ρ0, ρ2)?

The author-hosted source is <https://yupanliu.info/assets/pdf/PhD_thesis.pdf>.
The same triangle assertion appears in §1.3, “Improved inequalities on the quantum
triangular discrimination”, of *Quantum state testing beyond the polarizing regime
and quantum triangular discrimination*, arXiv:2303.01952v5, published in
*Computational Complexity* 34 (2025), article 11. The number 8.16 belongs to the
thesis, rather than to the journal article.

Definition 3.1 of arXiv v5 uses

$$
Q(A,B)=\frac12\operatorname{Tr}\bigl((A-B)(A+B)^{-1/2}(A-B)(A+B)^{-1/2}\bigr),
$$

with the inverse taken on the support. A state is a positive semidefinite complex
matrix of trace one. The order of the noncommuting factors is retained.

## Motivation

The thesis contrasts the conjecture with the metric property of the square root
of classical triangular discrimination, attributed there to Le Cam [LC86]. A
quantum metric would give three-point error control for the same divergence used
in the paper's state-testing comparisons.

## Gap

The triangle assertion quantifies over all finite dimensions and all state
triples, including rank-one endpoints. A two-dimensional family can test whether
a single constant controls the ratio of one side to the other two.

## Route

For $0<t\le1/4$, let

$$
\rho_\pm=\frac1{1+t^6}
\begin{pmatrix}1&\pm t^3\\\pm t^3&t^6\end{pmatrix},
\qquad \tau=\operatorname{diag}(1-t^4,t^4).
$$

The endpoints are normalized rank-one positive matrices. The intermediate state
is positive definite. Their pairwise sums are positive definite, so every inverse
square root used here is an ordinary inverse on the whole qubit space.

The diagonal endpoint sum gives

$$
Q(\rho_+,\rho_-)=\frac{2t^3}{1+t^6}.
$$

For a short edge, put $a=t^6/(1+t^6)$, $b=t^4$,
$d=\sqrt{b(2-b)+(1-2b)a}$, $u=b^2+(1-2b)a$ and $v=b(1-b)$.
The positive square-root certificate for a two-by-two positive definite matrix $S$ of trace
two is $(S+dI)/\sqrt{2+2d}$, with $d^2=\det S$. Its inverse is
$((2+d)I-S)/(d\sqrt{2+2d})$. Applying
$\operatorname{Tr}(M^2)=(\operatorname{Tr}M)^2-2\det M$ to
$M=(\rho_+-\tau)(\rho_++\tau)^{-1/2}$ yields

$$
Q(\rho_+,\tau)=Q(\tau,\rho_-)
=\frac ud+\frac{v^2}{d^2(1+d)}
\le\frac{83}{48}t^4<\frac74t^4.
$$

The scalar estimates are $d^2\ge3t^4/2$, $d\ge t^2$,
$u\le17t^6/16$ and $v^2\le t^8$.

## Falsifier

Given any real $K$, set $M=\max(K,1)$ and $t=1/(8M^2)$. Then

$$
4M^2\frac74t^4=\frac78t^3<t^3
\le Q(\rho_+,\rho_-).
$$

Taking nonnegative square roots and using the two short-edge bounds gives

$$
K\bigl(\sqrt{Q(\rho_+,\tau)}+\sqrt{Q(\tau,\rho_-)}\bigr)
<\sqrt{Q(\rho_+,\rho_-)}.
$$

In particular $K=1$ refutes the proposed triangle inequality. This family also
excludes every finite uniform quasi-triangle constant.

## Evidence

`D5/S3/Divergence/QuantumTriangularMetricRefutation.lean` imports the existing
`QuantumTriangularJensenShannonRefutation.QTD` and
`CoherenceL1RelativeEntropyBound.IsState`. Its public `claim` retains the full
finite-dimensional triple-state assertion; `no_quasi_triangle` gives the stronger
qubit statement for every real constant; `result : ¬ claim` consumes its instance
at one. The other definitions and lemmas are private.

The positive square root of each two-by-two sum is identified by
`CommutingMidpoint.Fidelity.sqrt_trace_square_two` and `sqrt_times_trace_two`;
a product check together with `AlternativeMeanLinearization.half_eq_sqrt` and
`half_inverse` then identifies the inverse square root. The diagonal CFC
calculation and two-by-two trace identity are reused from their existing owners.

The proofs use only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Triage

1. **Proved (Lean) — the metric assertion fails.** Dimension two already refutes
   the universal triangle inequality for the source's exact QTD definition.
2. **Proved (Lean bounds; paper interpretation) — the mechanism separates scales.** The rank-one endpoints have
   coherence of order $t^3$ and the full-rank diagonal intermediate state has
   noise $t^4$. The proved long-edge formula is of order $t^3$ and the short-edge
   upper bound is of order $t^4$. The low commutator norm does not prevent this
   noncommuting inverse-square-root effect.
3. **Proved (Lean) — no uniform quasi-triangle constant exists.** The theorem
   quantifies over every real $K$, rather than over a finite set of tests.
4. **Literature — the classical contrast.** The thesis cites Le Cam (1986),
   [LC86], for the metric property of the square root of classical triangular
   discrimination. That classical theorem is not formalized here.
5. **Paper-proved; not separately formalized — every fixed positive power fails.**
   For the same family with $0<t\le 1/4$, the long edge is at least
   $(32/17)t^3$ and each short edge is less than $(7/4)t^4$.
   Indeed, the long-edge formula is $2t^3/(1+t^6)$ and
   $1+t^6\le17/16$; the short-edge formula also makes both short edges
   strictly positive. Thus, for every fixed $\alpha>0$,
   $$
   \frac{Q(\rho_0,\rho_2)^\alpha}
        {Q(\rho_0,\rho_1)^\alpha+Q(\rho_1,\rho_2)^\alpha}
   >\frac12\left(\frac{128}{119}\right)^\alpha t^{-\alpha},
   $$
   which is unbounded as $t\downarrow0$. Hence $Q^\alpha$ has no uniform
   quasi-triangle constant for any fixed positive $\alpha$. These are paper
   consequences of the proved scale bounds, with no separate Lean theorem.
6. **Literature, limited to the checked passages — the proved source results
   are unaffected.** The arXiv v5 footnote and the corresponding thesis passage
   describe QTD as only “(conjectured to be) the squares of a metric”. Before
   Lemma 4.12 (thesis Lemma 7.30), the author explicitly contrasts the trace
   distance argument, which relies on the triangle inequality, with the QTD
   argument, which “circumvents this barrier by leveraging the inequalities
   between QTD and the Bures distance”. The QTD error reduction of Lemma 4.12
   therefore does not depend on the metric conjecture and is unaffected by its
   refutation; no other result of the source was audited for such dependence.
7. **Proved (Lean refutation; paper consequence) — the conjectural metric
   description fails.** The assertion that $\sqrt{\mathrm{QTD}}$ is a metric,
   including the QTD part of the footnote's conjectural description, is refuted.
   A trace-distance-style argument that requires the triangle inequality cannot
   be transferred to QTD using that conjecture. This conclusion concerns QTD;
   it does not settle the analogous assertion for measured QTD.
8. **Open — priority beyond the checked literature.** The source comparison
   concerns Liu's Definition 3.1. Jensen-gap quantum divergences and the distinct
   extension $1-F$ do not establish this assertion. No novelty or priority claim
   follows from the formal refutation.

## ASSUMED-UNVERIFIED

The classical Le Cam theorem is cited through the thesis and is not separately
formalized. Other powers have no separate Lean statement in this module. The literature search
found no settlement of Liu's exact assertion in the checked public sources;
this does not cover unpublished work or an inaccessible conference contribution.
