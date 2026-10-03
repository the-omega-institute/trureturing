---
slug: manetti-ricciardi-2015-higher-antibracket-coefficients
bibkey: manetti2016antibrackets
doi: 10.3842/SIGMA.2016.053
url: https://arxiv.org/abs/1509.09032v3
triage: theorem
motivation_gids:
  - D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.result
---

# The closed form of the higher-antibracket coefficients

## Problem

M. Manetti and G. Ricciardi, *Universal Lie Formulas for Higher
Antibrackets*, SIGMA 12 (2016), 053, arXiv:1509.09032v3, Conjecture 2.4:

> For every $n\ge 2$ the coefficients $c^n_i$ of Theorem~{\rm \ref{thm.standardform}} are given by the formula

$c_i^n=\frac{\displaystyle (-1)^{n} \prod_{j=2}^{i}\dfrac{n(n-1)-(j-1)(j-2)}{2}}{\displaystyle \sum_{h=2}^n h\left(\prod_{j=2}^{h}\dfrac{n(n-1)-(j-1)(j-2)}{2}\right)\left(\prod_{j=h}^{n-1}\dfrac{(1-j)(j+2)}{2}\right)}$,

> where every empty product is intended to be equal to $1$. Moreover $(-1)^{n}c^n_i>0$ for every $n\ge i\ge 1$.

The coefficients of Theorem 2.3 are the unique rationals with
$\Phi^{n+1}_f=(c_1^n\rho_1^n+c_2^n\rho_1^{n-2}\rho_2+\dots+c_n^n\rho_n)f$ for
every linear operator $f$ of every graded commutative algebra. The paper
proves Theorem 2.3 from Theorem 6.4, the same identity
$\Phi^{n+1}=(c_1^n\rho_1^n+\dots+c_n^n\rho_n)\Phi^1$ for the operators
$\Phi^{m,i}$ and $\rho_k$ on $\mathbb{Q}[x]$, through the $\mathfrak g$-module
morphism of Lemma 6.3; uniqueness in Theorem 2.3 identifies the two
sequences. The authors verified the formula for $n\le12$.

## Motivation

Higher Koszul brackets (higher antibrackets) measure the failure of an
operator to be a derivation and govern the BV formalism. Theorem 2.3
reduces every bracket $\Phi^{n+1}_f$ to iterated commutators with the
multiplication operators, with only the monomials
$\rho_1^{n-i}\rho_i$; the conjecture makes these universal Lie formulas
explicit. The frozen declaration
`D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.result` proves it.

## Gap

Issue #12104 classifies the conjecture as Tier 1 and records the literature
checks before any Lean:

- arXiv v3, the journal version, still states the conjecture;
- OEIS A272688 (revision 8, 2025-11-05) records the diagonal values
  $x_n^n=(-1)^n n!\,c_n^n$ and calls the formula conjectural;
- the citing works arXiv:1512.05480, 2012.14812, 2206.02048, 2407.16348,
  2409.09809, 2601.19698 and 1703.00290 do not address the coefficients;
- an adversarial search of equivalent formulations (Koszul brackets,
  higher derived brackets, loop homotopy algebras, Bessel and Legendre
  coefficient tables) and of the authors' later work found no settlement.

These are orchestrator-reported readings, `not-found-in-searched-scope`;
they do not establish exhaustive worldwide novelty.

## Route

Record the coefficient of $x^d/d!$ in $\Psi(x^s)$ as the lattice point
$(d,s)$.

1. From the definitions,
   $\rho_k(d,s)=\alpha_k(d)\,(d+k,s)-\binom{s+k}{k+1}(d,s+k)$ with
   $\alpha_k(d)=\binom{d+k}{k}-\binom{d+k}{k+1}$, and
   $\rho_i\Phi^1=(i,1)-(0,i+1)$.
2. The two moves of $\rho_1$ commute, so $\rho_1^t$ of a point is a
   binomial sum over paths, weighted by products $A$ of
   $\alpha_1(u)=(u+1)(2-u)/2$ and $B$ of $-\binom{u+1}{2}$.
3. The identity becomes $n+1$ linear equations, one for each point
   $(d,n+1-d)$. Since $\alpha_1(2)=0$, the equations with $d\ge3$ involve
   only $c_3,\dots,c_d$ and are triangular; the equations $d=0,1$ then fix
   $c_1,c_2$. This proves uniqueness.
4. For $n\ge3$ put
   $c_i=(-1)^n\dfrac{(n+i-2)!}{(n-i)!\,2^{i-1}}\cdot\dfrac{2^{n-1}}{(n-2)!\,(n+1)!}$.
   Every equation reduces to
   $\sum_{i}(-1)^{M-i}\binom{M}{i}\binom{i+a}{b}=\binom{a}{b-M}$ for
   $M\le b$ and $0$ for $M>b$, the iterated forward difference of
   $x\mapsto\binom{x}{b}$ given by Mathlib's `fwdDiff_iter_choose`.
5. The printed product equals $(n+i-2)!/((n-i)!\,2^{i-1})$, and by the same
   sum the printed denominator equals $(n-2)!(n+1)!/2^{n-1}$ for $n\ge3$.
6. For $n=2$ the equations give $c_1=c_2=1/2$, which is the printed value.
7. For $n=1$ the two equations give $c_1^1=-1$.
8. The sign clause for $n\ge i\ge1$ follows from the factorial form and
   from $c_1^1=-1$.

## Falsifier

The kernel-checked `result` states three parts: for every $n\ge2$ a
sequence satisfies the identity of Theorem 6.4 if and only if it agrees with
the printed formula on $1\le i\le n$; for $n=1$ it satisfies the identity if
and only if $c_1=-1$; and for every $n\ge1$ every solution has
$(-1)^n c_i>0$ for $1\le i\le n$. A different normalization of $\rho_k$, of $\Phi^{m,i}$, or of
the sign of $\Phi^m$ changes the question.

## Evidence

An independent SymPy recomputation from the raw definitions (operators on
$x^0,\dots,x^{n+1}$, exact rationals) finds a unique solution for each
$n=2,\dots,13$ and no mismatch with the printed formula; it reproduces the
paper's Table 1 (for example $4/5,24/5,24,72$ at $n=4$) and OEIS A272688,
and a perturbed target $\Phi^6+\Phi^{6,1}$ has no solution (issue #12104).

The canonical source is
`D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.lean`. Its public
declarations are `phi`, `koszul`, `rho`, `formula`, `claim` and `result`.
The frozen module state has statement identity `sha256:6998dc0e291c064a2c343c9a4821335d47a6c2dc056684232f87b75b7c720aad`. The
result declaration has statement identity `sha256:bee22258d60b9bfd38ae17b3a86112a02384da8fdd4fa30347e9519cd18b3b73`. The Freeze
event is `sha256:1f3e9e157898a2ab02b0c9f4da7ff57cf30523b12f743fc7376af7647af01c3c`. It has no project-level frozen prerequisites
(pinned Mathlib only). The proof uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new
axiom.

## Triage

Tier 1 published conjecture; resolution `Proved` by
`D5/S3/HomologicalAlgebra/HigherAntibracketCoefficients.result`.
`proof_shape: content`; `admission_basis: open-problem-resolution` (issue
#12104). Utility kind `none` (a general theorem for all $n$).

### What the settlement shows

- **Proved by `result`:** for every $n\ge2$ the coefficients are the
  unique solution of the identity and equal the printed formula; for $n=1$
  the unique solution is $c_1^1=-1$; and $(-1)^n c_i^n>0$ for every
  $n\ge i\ge1$.
- **Proved inside the proof of `result`:** for $n\ge3$,
  $c_i^n=(-1)^n\,2^{n-i}\dfrac{(n+i-2)!}{(n-2)!\,(n+1)!\,(n-i)!}$, and the
  printed denominator equals $(n-2)!(n+1)!/2^{n-1}$; it equals $2$ for
  $n=2$.
- **Follows from the closed form (not stated in Lean):** consecutive
  coefficients satisfy $c_{i+1}^n/c_i^n=(n-i)(n+i-1)/2$ for $n\ge3$ and
  $1\le i<n$.
- **Mechanism:** $\alpha_1(2)=0$, so $\rho_1$ cannot move a coordinate from
  $d=2$ to $d=3$. The paths from $(0,i+1)$ stop at $d\le2$, the equations
  with $d\ge3$ see only the paths from $(i,1)$ with $i\ge3$, and the
  coefficient system is triangular. All remaining sums are iterated forward
  differences $\sum_i(-1)^{M-i}\binom Mi\binom{i+a}b$, equal to
  $\binom a{b-M}$ for $M\le b$ and to $0$ for $M>b$ (Route, step 4); the
  printed denominator uses the case $M=b$, where the value is $1$.
- **Follows from the proved closed form:** the diagonal of OEIS A272688 is
  $x_n^n=(-1)^n n!\,c_n^n=\dfrac{n!\,(2n-2)!}{(n-2)!\,(n+1)!}$ for $n\ge3$
  (and $1$ at $n=2$).
- **Unchanged:** the paper's Theorems 2.1, 2.3 and 6.4 do not depend on the
  conjecture; with it, every higher antibracket
  $\Phi^{n+1}_f=\sum_i c_i^n\rho_1^{n-i}\rho_i f$ has explicit rational
  coefficients.
- **Open here:** closed forms for normal forms with other orderings of the
  $\rho_k$ (for example $\rho_i\rho_1^{n-i}$), and for the noncommutative
  brackets of the paper's Remark 5.6.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority or absence of an
independent answer; the full texts of Manetti's *Lie Methods in Deformation
Theory* (2022) and of Dijoux (2020) were not accessible. The Lean kernel
verifies the encoded statement and its axiom closure; its correspondence to
the paper, including the reading of the coefficients of Theorem 2.3 as the
unique solution of Theorem 6.4 and the statement inside
$\mathrm{End}_{\mathbb Q}(\mathbb Q[x])$ rather than the subalgebra
$\mathfrak a$, is checked by reading the source and the definitions.
