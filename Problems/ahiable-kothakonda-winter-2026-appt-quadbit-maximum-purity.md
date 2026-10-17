---
slug: ahiable-kothakonda-winter-2026-appt-quadbit-maximum-purity
bibkey: ahiablekothakondawinter2026geometry
doi: 10.48550/arXiv.2608.03390
url: https://arxiv.org/abs/2608.03390v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity.result
---

# Maximum purity in the 4-by-4 absolutely PPT sector

## Problem

Ahiable, Kothakonda and Winter, arXiv:2608.03390v2, Conjecture 6.7, page 29:

> Let $\mathcal P_{m,n}\subseteq\mathrm{APPT}_{m,n}$ be the inscribed absolute PPT polytope with $2\leq m\leq n,\;n>2$. Then
> $$\max_{\lambda\in\mathrm{APPT}_{m,n}}\sum_{i=1}^{mn}\lambda_i^2
> =\max_{\lambda\in\mathcal P_{m,n}}\sum_{i=1}^{mn}\lambda_i^2$$
> and occurs at the spectra given by Eq. (44).

The exact target here is its $m=n=4$ sector. A density matrix is a complex
matrix $\rho$ on $\mathbb C^4\otimes\mathbb C^4$ with $\rho\succeq0$ and
$\operatorname{Tr}\rho=1$. Literal APPT requires
$(U\rho U^\dagger)^\Gamma\succeq0$ for every global unitary $U$, where
$\Gamma$ transposes the second tensor factor.

## Motivation

Corollary 6.4 and Eq. (44) give the candidate purity
$(16+8)/(16+2)^2=2/27$, attained within the inscribed polytope at the spectrum
$(1/6,1/18,\ldots,1/18)$. An attaining state alone supplies a lower bound.
The missing direction is an upper bound for every literal APPT density
matrix, followed by equality of the real purity supremum with $2/27$.

## Gap

Research preregistration [#17689](https://github.com/the-omega-institute/trureturing/issues/17689)
fixes this sector before the new upper-bound probes. The source states the
general conjecture and gives numerical evidence for local dimension four.
Tran, arXiv:2609.18568v1, remark following Theorem A, records the exact APPT
purity gap. The existing qutrit dossier settles $m=3$ and leaves higher local
dimensions open. No $4\otimes4$ upper bound was found in the searched source
records or current owning library. This is a tier-3 research target and a
`not-found-in-searched-scope` statement, not a worldwide priority certificate.

## Route

An explicit $3\otimes3$ Bell corner inside $4\otimes4$, with an identity on
the seven-dimensional complement, gives two necessary real $3\times3$
boundary LMIs. The corner uses the three largest and six smallest ordered
eigenvalues. It does not require a sufficient spectral characterization of
APPT in local dimension four.

Let $\lambda_0\geq\cdots\geq\lambda_{15}\geq0$, with sum one, and put
$t=\lambda_9$, $P=\sum_i\lambda_i^2$. The first LMI tested at $(1,1,1)$ gives
$\lambda_0+\lambda_1+\lambda_2\leq\sum_{i=10}^{15}\lambda_i$; ordering and
mass one then give $13t\leq1$.

If $t\leq1/18$, insert two copies of $t$ to get an ordered 18-vector. If
$t\geq1/18$, delete $t$ to get an ordered 15-vector. The boundary matrices
are unchanged before normalization. Positive normalization and the existing
`QutritN6PurityBound.certificate_bound` and
`QutritN5PurityBound.certificate_bound` give, respectively,

$$P\leq\frac{26}{400}(1+2t)^2-2t^2,\qquad
P\leq\frac{23}{289}(1-t)^2+t^2.$$

The first expression is at most $2/27$ on $[0,1/18]$. For the second,

$$\frac{23}{289}(1-t)^2+t^2-\frac{2}{27}
=\frac{312}{289}\left(t-\frac1{18}\right)
 \left(t-\frac{43}{468}\right),$$

which is nonpositive on $[1/18,1/13]$. The original certificate bodies are
reused directly, rather than copied or replaced by numerical estimates.
The explicit attaining state uses the existing dimension-independent
`LowRankRays.separableCone_one_add_two_rankOne` theorem.

## Falsifier

A PSD trace-one $4\otimes4$ matrix satisfying the literal unitary-quantified
APPT condition and having real trace-square greater than $2/27$ would refute
the target. Repeated eigenvalues and zero eigenvalues are included. Neither
simple spectrum nor strict positivity is a hypothesis.

## Evidence

`QuadbitMaximumPurity.result : claim` has passed the canonical scoped Lean
build together with `QuadbitSpectralPurityBound.spectral_purity_bound`. The
claim includes the universal bound, real supremum and explicit diagonal
attainment. Both printed axiom closures contain only `propext`,
`Classical.choice` and `Quot.sound`; the proof introduces no additional axiom.
The current scoped report covers both the mathematical root and its Reg
mirror, with 91 project modules, and checks every extracted axiom closure.
It reports the complete result registration as `declared_validated` with
`source-equivalence`, no diagnostic, and an unknown continuation. Official
required CI is checked at delivery. A mathematical and statement-fidelity review by another agent of
the same model family found no gap; an earlier Oracle authentication failure
yielded no Pro review.

The source-owner escape registrations for newly exposed supporting theorems
remain unfinished and are disclosed in [#17689](https://github.com/the-omega-institute/trureturing/issues/17689).
That audit issue does not supply any mathematical premise or establish a
registration verdict.

## Triage

**Proved in Lean for the stated sector.** Official required CI remains part
of delivery verification; its outcome is not inferred from the local build.

**Mechanism.** Both necessary boundary LMIs observe only nine extremal
coordinates. Inserting or deleting an interior coordinate preserves that
observation, allowing certificates at adjacent total dimensions to control
a new tensor-factor sector. The proved spectral estimate therefore has
weaker hypotheses than literal APPT, and the final theorem discharges
those hypotheses from literal APPT.

**Outside scope.** The other $m=4$ sectors, all $m\geq5$, a classification
of every maximizer, and APPT versus absolute separability are not settled
by this target. No downstream source theorem outside the stated sector is
claimed as formalized.

## ASSUMED-UNVERIFIED

Worldwide novelty and absence of an independent post-source settlement are
not kernel facts. The earlier Oracle request failed authentication and gave
no Pro result. Source provenance is recorded in the existing library notes;
the mathematical theorem uses the literal density and APPT predicates and
does not assume a sufficient four-dimensional Hildebrand characterization.
