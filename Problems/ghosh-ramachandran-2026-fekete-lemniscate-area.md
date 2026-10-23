---
slug: ghosh-ramachandran-2026-fekete-lemniscate-area
bibkey: ghosh2026erdos
doi: 10.1090/proc/17897
url: https://arxiv.org/abs/2604.03036v3
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.result
---

# Ghosh–Ramachandran's connected-set Fekete area question

## Problem

S. Ghosh and K. Ramachandran, *A note on the Erdős minimal area problem*,
arXiv:2604.03036v3, immediately after Proposition 3.6:

> While the above proposition proves that Fekete polynomials are not area minimizers in general, it would be of interest to know if they are minimzers when the set $K$ is connected. We leave this as an open question.

In Section 1, $P_n(K)$ consists of monic degree-$n$ polynomials whose
zeros all lie in the compact set $K\subseteq\mathbb C$.
Write $\Lambda_p=\{z:|p(z)|<1\}$ and
$A_n(K)=\inf_{p\in P_n(K)}m(\Lambda_p)$, with $m$ planar Lebesgue measure.
A Fekete tuple $a=(a_1,\ldots,a_n)$ maximizes
$\prod_{i<j}|a_i-a_j|$ on $K^n$, and defines
$F_a(z)=\prod_i(z-a_i)$.

The Lean `claim` says that for every compact connected $K$, every
$n\geq1$, every Fekete tuple $a$ in $K$, and every $p\in P_n(K)$,
$m(\Lambda_{F_a})\leq m(\Lambda_p)$. Thus `result : ¬ claim` refutes
exact area minimization in the stated connected-set setting.

## Motivation

Theorem 3.1 gives logarithmic-scale asymptotic optimality for
$\operatorname{cap}(K)>1$. Exact minimization is a stronger assertion.
The declaration
`D5/S3/Analytic/Lemniscates/FeketeLemniscateAreaRefutation.result`
exhibits a connected compact interval where a degree-four competitor
has strictly smaller unit-lemniscate area than a Fekete polynomial.

## Gap

The source leaves the connected case as an open question; the paper's
Proposition 3.6 uses the disconnected set $2\overline{\mathbb D}\cup\{a\}$.
No later answer was found: arXiv:2606.17097 (sharp order in Erdős's
minimum-area problem) does not mention Fekete polynomials or this
question; keyword searches of the arXiv listings, the web,
conjectures.io and Formal Conjectures return no entry for it. The
source note is `Library/Geometry/ghosh2026erdos.md`.

## Route

Take $K=[-20,20]$ embedded in $\mathbb C$, and $n=4$. For every $R>0$,
the tuple $(-R,-u,u,R)$ with $u>0$ and $5u^2=R^2$ is Fekete on
$[-R,R]$. Its maximal Vandermonde product is

$$
4Ru(R^2-u^2)^2=\frac{64R^6}{25\sqrt5}.
$$

At $R=20$, this gives $u=\sqrt{80}$ and
$F(z)=(z^2-400)(z^2-80)$. Use the competitor
$G(z)=(z^2-400)(z^2-100)$, whose roots are $\pm20,\pm10$.

| Certificate | Centres | Radius at each centre |
| --- | --- | --- |
| Disjoint discs inside $\Lambda_F$ | $\pm20$ | $97/1250000$ |
| Disjoint discs inside $\Lambda_F$ | $\pm\sqrt{80}$ | $217/1250000$ |
| Discs covering $\Lambda_G$ | $\pm20$ | $53/625000$ |
| Discs covering $\Lambda_G$ | $\pm10$ | $849/5000000$ |

The inner certificate uses
$r_k\prod_{j\ne k}(|a_k-a_j|+r_k)<1$.
The outer certificate uses the general three-regime cover lemma with
$e=1/10$ and $t=5$. Summing disc areas gives the exact rational bounds

$$
m(\Lambda_F)\geq\pi\frac{7231744}{10^{14}}
=\pi\,7.231744\cdot10^{-8}
>\pi\,7.204616\cdot10^{-8}
=\pi\frac{7204616}{10^{14}}\geq m(\Lambda_G).
$$

## Falsifier

The strict area comparison on this single connected compact interval
falsifies the universal minimization claim. The competitor is monic,
has degree four, and has all roots in $K$. The proof also certifies the
Fekete property, the inner-disc disjointness, and the outer cover;
these conditions are required for the area comparison to address the
source question.

## Evidence

The committed Lean module defines `vandermonde`, `IsFeketeTuple`, `InP`,
`lemniscateArea` and `claim`. Its public theorems are
`isFeketeTuple_interval_four`, `ball_subset_lemniscate`,
`lemniscate_subset_balls` and `result : ¬ claim`.
The exact rational disc bounds, compactness, connectedness and admissible
competitor establish the contradiction. The accepted axiom closure is
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$;
there is no `sorry` or additional axiom.

The supplied numerical calculation uses `mpmath` radial integration and
gives $m(\Lambda_F)\approx2.30097118\cdot10^{-7}$ and
$m(\Lambda_G)\approx2.18166157\cdot10^{-7}$. These are computed values,
not the rational certificate used by Lean; no certified numerical error
bound is supplied.

## Triage

### What the settlement shows

1. **Proved (Lean) — general mechanisms.** `ball_subset_lemniscate`
   puts a disc inside the unit lemniscate of an arbitrary finite root
   family under its product bound. `lemniscate_subset_balls` covers the
   lemniscate of a nonempty root family under separation and three
   distance-regime bounds. `isFeketeTuple_interval_four` proves that
   $(-R,-R/\sqrt5,R/\sqrt5,R)$ is Fekete for every $R>0$.
   This theorem exhibits maximizers; it does not classify all maximizers.

2. **Computed — numerical areas.** `mpmath` radial integration gives
   $m(\Lambda_F)\approx2.30097118\cdot10^{-7}$ and
   $m(\Lambda_G)\approx2.18166157\cdot10^{-7}$. The strict comparison
   in `result` relies on the rational disc certificate, independently
   of these numerical approximations.

3. **Open here — small-level asymptotics and scaling.** For a polynomial
   with simple zeros $a_i$, the proposed relation is

   $$
   \frac{m\{z:|p(z)|<t\}}{\pi t^2}
   \longrightarrow\sum_i|p'(a_i)|^{-2}\qquad(t\downarrow0).
   $$

   **Computed — derivative sums.** For
   $f(z)=(z^2-1)(z^2-1/5)$ and $g(z)=(z^2-1)(z^2-1/4)$,
   $S(f)=75/16>40/9=S(g)$, where $S(p)=\sum_i|p'(a_i)|^{-2}$.
   **Open here (heuristic) — interval family.** With
   $F_R(z)=R^4f(z/R)$ and $G_R(z)=R^4g(z/R)$, the level is $R^{-4}$
   and the area scaling factor is $R^2$. The proposed asymptotic relation
   would imply that every sufficiently large $R$ gives a degree-four
   counterexample on $[-R,R]$. Neither the limiting relation nor this
   uniform eventual statement is proved here.

4. **Open (heuristic) — every even degree.** A proposed extension to
   every even $n\geq4$ is based on incompatibility of the unweighted
   Fekete balance equations with the weighted stationarity equations
   of $\sum_i|p'(a_i)|^{-2}$. Such incompatibility and a corresponding
   family of finite certificates remain unproved here.

5. **Proved — exact optimality fails for connected sets.** The
   counterexample prevents upgrading the paper's Theorem 3.1
   logarithmic asymptotic conclusion to universal exact optimality,
   even when $K$ is connected. **Proved (paper, Theorem 3.1) —
   the logarithmic conclusion survives.** Theorem 3.1 for
   $\operatorname{cap}(K)>1$ is not contradicted by this finite example.
   **Open (heuristic) — local explanation.** The derivative sums suggest
   a local obstruction at the zeros rather than a topological one;
   the Lean certificate proves that disconnectedness of $K$ is not
   necessary, without proving the derivative-weight asymptotic mechanism.

6. **Open — neighbouring exact-minimization questions.** Are Fekete
   polynomials exact minimizers for connected $K$ with
   $\operatorname{cap}(K)\leq1$, or for the closed unit disc?
   Does the answer change when the level $t$ is required to make
   $\{z:|p(z)|<t\}$ connected? The present unit-level interval
   counterexample settles none of these restrictions.

## ASSUMED-UNVERIFIED

The forward-citation list of arXiv:2604.03036 was not obtained in
full, so an answer in a citing paper outside the searched listings is
not excluded. The numerical areas carry no certified error bound.
Small-level asymptotics, the eventual large-interval family, the
derivative-weight explanation and the extension to every even degree
are not proved.
