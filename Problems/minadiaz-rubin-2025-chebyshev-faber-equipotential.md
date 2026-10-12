---
slug: minadiaz-rubin-2025-chebyshev-faber-equipotential
bibkey: minadiaz2025chebyshev
doi: null
url: https://arxiv.org/abs/2505.03967v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.result
---

# Miña-Díaz–Rubin's Chebyshev–Faber equipotential question

## Problem

E. Miña-Díaz and O. Rubin, *Chebyshev polynomials on equipotential
curves*, arXiv:2505.03967v1, Section 2, Problem 2.2:

> Suppose the compact set $K$ is such that for some $n\in\mathbb N$, $T_{n,K}=\hat F_n$, where $\hat F_n$ is the $n$th monic Faber polynomial associated to the map $\phi$ that satisfies (1.2). Is it true then that $T_{n,L_r}=\hat F_n$ for all $r>1$?

Here $\Omega$ is the unbounded component of $\mathbb C\setminus K$,
$g_\Omega(z,\infty)=\log|\phi(z)|$, and
$\phi(z)=cz+c_0+c_{-1}/z+\cdots$, with
$c=\operatorname{cap}(K)^{-1}$. When $\Omega$ is simply connected,
$\psi=\phi^{-1}$. The equipotential curve is
$L_r=\{z\in\Omega:|\phi(z)|=r\}=\psi(\{|w|=r\})$.
The polynomial $F_n$ is the polynomial part of $\phi^n$ at infinity,
$\hat F_n=c^{-n}F_n$, and $T_{n,E}$ is the unique monic degree-$n$
sup-norm minimizer on $E$.

The Lean `claim` quantifies over exterior maps $\psi$ differentiable
and injective on $|w|>1$, a positive capacity $\kappa=1/c$, compact
complement $K$, and a bounded correction $\psi(w)-\kappa w$ for
$|w|>2$. Its `IsMonicFaber` requires a monic degree-$n$ polynomial
$F$ with $F(\psi(w))-(\kappa w)^n\to0$ at infinity. Its
`IsChebyshev` compares every uniform real bound for every monic
degree-$n$ competitor. For compact nonempty sets this expresses
sup-norm minimization. The implication asks whether such an $F$
Chebyshev on $K$ remains Chebyshev on every $L_r$, $r>1$.

## Motivation

Theorem 2.1 gives $T_{n,L_r}\to\hat F_n$ as $r\to\infty$.
Equality at every finite radius is stronger than this limit.
The declaration
`D5/S3/Analytic/Chebyshev/FaberEquipotentialRefutation.result`
proves `¬ claim` with $n=1$, $\kappa=1$ and $r=2$.

## Gap

Preregistration [#15412](https://github.com/the-omega-institute/trureturing/issues/15412)
identifies the tier-1 question and its refutation. Rubin's *Chebyshev
polynomials in the complex plane and on the real line*,
arXiv:2411.14175v2, revised 2026-02-18, still lists it as Problem 5.6.
Hübner–Rubin, arXiv:2405.05067, gives
rotation-symmetric examples with $T=\hat F=z^\ell$ preserved on
equipotentials. Miña-Díaz–Rubin–Wennman, arXiv:2509.22588, concerns
$n\to\infty$ asymptotics and does not supply the fixed-degree
propagation assertion.

Xiao–Qiu, *Acta Mathematica Sinica, Chinese Series* 53(2) (2010),
323–328, gives an example where Chebyshev polynomials on a Julia set
and its equipotentials differ. Whether that example has $T=\hat F$
on the Julia set is **ASSUMED-UNVERIFIED** because its full text was
not available. The centre criterion is discussed in Triage. These
references do not establish an exhaustive priority claim. The source note is
`Library/Geometry/minadiaz2025chebyshev.md`.

## Route

Take

$$
\psi(w)=w+\frac1{4w}+\frac1{100}(w^{-2}-w^{-4}),\qquad
K=\mathbb C\setminus\psi(\{|w|>1\}).
$$

For $|u|,|v|\geq1$, the proof establishes

$$
|\psi(u)-\psi(v)-(u-v)|\leq\frac{31}{100}|u-v|.
$$

This proves injectivity on the closed exterior and two-sided bounds
$|\psi(u)-\psi(v)|\leq(131/100)|u-v|$ and
$|u-v|\leq2|\psi(u)-\psi(v)|$. Differentiability and the complex
open mapping theorem make the open exterior image open; the
two-sided bounds make the closed exterior image closed. Connectedness
of the exterior of a disc then gives
$K\subseteq\overline{B}(0,5/4)$ and compactness.
Injectivity on the closed exterior puts
$\psi(\pm1)=\pm5/4$ in $K$. The two opposite endpoints force every
degree-one monic competitor to have norm at least $5/4$, so $z$ is
Chebyshev on $K$. Also $\psi(w)-w\to0$, giving $\hat F_1=z$.

The private `circle_bound` proves, for every $r\geq1$ and $|w|=r$,

$$
\left|\psi(w)-\frac1{100}(r^{-2}-r^{-4})\right|
\leq r+\frac1{4r}.
$$

At $r=2$ the competitor $q(z)=z-3/1600$ therefore has norm at most
$17/8=3400/1600$. But $\psi(2)=3403/1600$ lies on $L_2$, so
$z$ has strictly larger norm there. The exact gap is $3/1600$.

## Falsifier

The single admissible exterior map, compact complement, degree-one
Faber polynomial and radius-two competitor falsify the universal
propagation assertion. A norm comparison without injectivity,
compactness, the Faber normalization or the initial Chebyshev property
would not address the source question; the proof supplies each.
No classification of the minimizer on every outer curve is required
for this radius-two contradiction.

## Evidence

The module's public definitions are `IsChebyshev`,
`IsMonicFaber` and `claim`; its only public theorem is
`result : ¬ claim`. Supporting declarations are private, including
`perturbation_lipschitz`, `injective_closed`, `exterior_bilipschitz`,
`compact_complement`, `circle_algebra_bound`, `circle_complex_bound`,
`circle_bound`, `chebyshev_of_disc` and `faber`.
The norm-square estimate in `circle_algebra_bound` controls the
cross term and residual term on a normalized circle. The proof uses
exact rational arithmetic, the frozen
`D5.S3.AnalyticClosure.ComplexPowerDifference.norm_pow_sub_pow_le`
at $H=1$, and the pinned Mathlib topological and complex-analytic
results. The consumed helpers `powers_lipschitz`, `perturbation_lipschitz`,
`injective_closed` and `exterior_bilipschitz` are bind-only; the
per-declaration inventory is in the Lean header. Its accepted axiom closure is
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$;
there is no `sorry` or additional axiom.

The odd-cubic computation in Triage covers $a\in\{-1,1,2\}$ and
$r\in\{1.5,2,3\}$, with agreement to $10^{-7}$.
No experiment program or certified numerical error bound is available;
this computed observation is separate from the Lean counterexample.

## Triage

### What the settlement shows

1. **Proved (Lean) — degree-one failure.** The map above has
   $T_{1,K}=\hat F_1=z$, but $z$ is not Chebyshev on $L_2$.
   The proof establishes Lipschitz injectivity, compactness and the
   enclosing-circle norm bound, including its general $r\geq1$ form.

2. **Open in Lean (analytic argument) — every radius.**
   Write $c_r=(1/100)(r^{-2}-r^{-4})$ and $R_r=r+1/(4r)$.
   The enclosing-disc bound and
   $\psi(\pm r)=c_r\pm R_r$ identify the minimal enclosing circle
   as the circle of centre $c_r$ and radius $R_r$. This gives
   $T_{1,L_r}=z-c_r\ne z$ for every $r>1$. The full minimizer
   identification and universal failure are analytic consequences
   not stated as Lean theorems in this module.

3. **Open here (not formalized; analytic argument) — every degree.**
   For each positive integer $d$, set $K_d=\{z:z^d\in K\}$.
   Rotation averaging, or the Kamo–Borodin / Novello–Schiefermayr–Zinchenko
   composition rule, gives the proposed extension

   $$
   T_{d,K_d}=\hat F_d=z^d,\qquad
   T_{d,L_r(K_d)}=z^d-c_{r^d}.
   $$

   The Green-function normalization is
   $g_{K_d}(z)=d^{-1}g_K(z^d)$; hence radius $r$ for $K_d$ maps
   to radius $r^d$ for $K$. The composition and Faber identifications
   are not formalized here.

4. **Open in Lean (analytic argument) — minimal-circle interpretation
   and centre drift for every $r>1$.** Degree-one minimization is the
   minimal enclosing circle problem. The perturbation
   $b(w^{-2}-w^{-4})$, $b=1/100$,
   contributes zero to the centre at $r=1$ and a positive $c_r$ for
   $r>1$; it need not vanish pointwise on the unit circle. Thus the
   initial equality does not fix the outer centres.
   **Literature-attested (paper, Theorem 2.1; not formalized here) —
   the limiting statement survives.** Since $c_r\to0$,
   the analytic family is consistent with $T_{n,L_r}\to\hat F_n$.

5. **Open here (composition argument not formalized) — Julia-set
   criterion.** For a monic polynomial
   $P(z)=z^m+a_{m-1}z^{m-1}+\cdots$, $m\geq2$, and centre $h$
   of the minimal enclosing circle of $J_P$, the composition rule gives
   $T_{m^k,J_P}=P^{\circ k}-h$, while
   $\hat F_{m^k}=P^{\circ k}+a_{m-1}/m$, for $k\geq1$.
   A counterexample through these degrees therefore needs
   $h=-a_{m-1}/m$ and an outer centre that drifts. A rotational
   symmetry of order at least two about that centre preserves it on
   equipotentials and prevents this mechanism.
   **Computed — numerical Julia-set probe.** For the odd cubics
   $z^3+az$ with $a\in\{-1,1,2\}$ on levels
   $r\in\{1.5,2,3\}$, the numerical probe found agreement to
   $10^{-7}$. There is no certified error bound; this is not a
   uniform result for all cubics.

6. **Open — additional hypotheses.** Does equality propagate when
   $K$ has rotational symmetry of order greater than $n$? Does it
   propagate for an analytic boundary if $T_{n,K}=\hat F_n$ for
   every $n$? These sufficient-condition questions are not settled
   by the Lean counterexample. The rotation-symmetric literature
   examples supply surviving special cases.

## ASSUMED-UNVERIFIED

The full text of Xiao–Qiu (2010) was not available. Whether its example
satisfies $T=\hat F$ on the Julia set,
equivalently the relevant enclosing-circle centre condition
$h=-a_{m-1}/m$, was not determined. Its reported difference between
Julia-set and equipotential Chebyshev polynomials alone does not
settle Problem 2.2.

No DOI is recorded, and exhaustive priority is not established.
Failure at every $r>1$, the every-degree pullback
extension, the Julia-set composition analysis and the additional-
hypothesis questions have no Lean theorem here. The odd-cubic
numerics have no experiment program or certified error bound.
