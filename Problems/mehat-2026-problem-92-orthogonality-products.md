---
slug: mehat-2026-problem-92-orthogonality-products
bibkey: mehat2026eulermagic
doi: null
url: https://arxiv.org/html/2609.05530v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Mehat/OrthogonalityProducts.problem92
---

# Mehat Problem 9.2: distinct products from integer orthogonality factors

## Problem

Sanjit Singh Mehat, *Tensor constructions for Euler magic matrices and proper
examples of orders 9, 27, 81 and 243*, arXiv:2609.05530v1, Section 9,
Problem 9.2 (`S9.Thmtheorem2`), asks:

> Do there exist, for every $k$, orthogonality factors $A_1,\dots,A_k$ of order
> $3$ whose $9^k$ products of entry squares are pairwise distinct?

Definition 2.1 (`S2.Thmtheorem1`) specifies an integer matrix $A$ satisfying
$AA^{\mathsf T}=\gamma I$ for a nonzero integer $\gamma$. The complete
positive-length assertion is: for every natural $k\geq1$, there exist
$A_i\in\mathbb Z^{3\times3}$ and $\gamma_i\in\mathbb Z\setminus\{0\}$,
for $i\in\{0,\ldots,k-1\}$, such that

$$
A_iA_i^{\mathsf T}=\gamma_i I_3
$$

and the map

$$
p\longmapsto\prod_{i=0}^{k-1}(A_i)_{p(i)_1,p(i)_2}^{\,2},
\qquad
p:\{0,\ldots,k-1\}\longrightarrow\{0,1,2\}^2,
$$

is injective. Distinct indexed choices must give different integer products,
even when their positions occur in different factors. Both matrices and
constants may depend on $k$. There is no bound on $k$ or the entries.

## Motivation

Distinct indexed products are the separation requirement in the paper's
orthogonality-factor construction. The motivating frozen declaration is the
full statement `D5/S3/Arith/Mehat/OrthogonalityProducts.problem92`.
This dossier concerns only Problem 9.2. Euler diagonal constraints and the
existence assertions of Problems 9.1 and 9.3 are separate questions.

## Gap

The cited version poses this assertion as a question. Its Lemma 2.4 supplies
the classical quaternion matrix, not the arbitrary-length product-separation
argument. The gap addressed here is simultaneous avoidance of every collision
between indexed products while preserving integer orthogonality factors.

The bounded source check covers the primary text, Definition 2.1, Lemma 2.4
and Problem 9.2. The Library note identifies the author's published Lean tree
at commit `b9b4821f2078fcd75c7786e760f336c7688ced30`; its toolchain and
Mathlib pins differ, and no source from that tree is transplanted. Broader
citing-paper, related-paper and general-search checks are incomplete. These
limits do not certify worldwide novelty, priority or the absence of an
independent resolution. The original-question registration is
[#30017](https://github.com/the-omega-institute/trureturing/issues/30017).

## Route

Write $R(x)$ for the integer quaternion matrix of Lemma 2.4, equation (4),
with four integer coordinates $x=(x_0,x_1,x_2,x_3)$, and write $f_e$ for
its entry polynomial at position $e\in E=\{0,1,2\}^2$. Direct polynomial
identities give

$$
R(x)R(x)^{\mathsf T}=(x_0^2+x_1^2+x_2^2+x_3^2)^2 I_3.
$$

Two elementary entry facts are used. Every $f_e(1,2,3,4)$ is nonzero. For
any ordered pair $e\ne d$, an integer tuple $z_{e,d}$ satisfies
$f_e(z_{e,d})=0$ and $f_d(z_{e,d})\ne0$. The complete finite certificate
is the table `separatingPoint` in the Lean source; `separatingPoint_spec`
checks every distinct pair by exact decision. This is a finite entry lemma,
not a finite replacement for the quantified problem.

Suppose $T$ is any finite index set and $P:T\to\mathbb Z$ is injective
with every $P(t)\ne0$. For distinct $(t,e),(s,d)\in T\times E$, set

$$
C_{(t,e),(s,d)}=P(t)f_e^2-P(s)f_d^2.
$$

Each collision polynomial is nonzero. If $e=d$, injectivity of $P$ and
$f_e\ne0$ imply this in the integral domain $\mathbb Z[X_0,X_1,X_2,X_3]$.
If $e\ne d$, evaluation at $z_{e,d}$ leaves the nonzero value
$-P(s)f_d(z_{e,d})^2$. Consequently the polynomial

$$
F=\left(\prod_{e\in E}f_e\right)
\prod_{\substack{a,b\in T\times E\\a\ne b}}C_{a,b}
$$

is nonzero. A polynomial over the infinite integral domain $\mathbb Z$
which vanishes at every integer tuple is zero; its contrapositive gives an
integer tuple $x$ with $F(x)\ne0$. Every entry $f_e(x)$ is then nonzero,
and all values $P(t)f_e(x)^2$ are pairwise distinct. Also $x\ne0$, so the
sum of its coordinate squares, and hence the orthogonality constant, is
nonzero.

Induct on the number of factors. At length zero there is one empty indexed
choice, with product $1$. Given factors of length $k$, let $T=E^k$ and
$P(p)=\prod_i(A_i)_{p(i)_1,p(i)_2}^2$. The induction maintains nonzero
entries, so $P$ is nonzero everywhere as well as injective. The preceding
construction adjoins $R(x)$ and proves these same properties at length
$k+1$, along with its required nonzero orthogonality constant. Thus the
construction works for every finite length, and in particular every $k\ge1$.

The Lean correspondence is exact: `Problem92` binds `k : ℕ` with `1 ≤ k`,
`A : Fin k → Matrix (Fin 3) (Fin 3) ℤ`, and `gamma : Fin k → ℤ`.
Its conjunction states nonzero constants and the matrix identities; its
`Function.Injective` argument ranges over all functions
`Fin k → Fin 3 × Fin 3`. `quaternionMatrix` defines $R$;
`collision_ne_zero` proves nonvanishing of the weighted differences;
`extend_products` uses `MvPolynomial.funext` through `integer_nonzero_point`
to obtain simultaneous avoidance. `factors_all` carries the full induction,
and the public `problem92 : Problem92` extracts the requested assertion.
There is no additional mathematical hypothesis.

## Falsifier

A counterexample would be a positive length $k$ for which every integer
family satisfying the orthogonality-factor equations has two different
indexed choices with equal products. It contradicts the exact universal
Lean conclusion. A discrepancy between the source's entry-choice meaning
and the displayed injectivity statement, an incorrect separation certificate,
or a nonstandard axiom dependency would invalidate the claimed correspondence.
No numerical experiment is used as evidence for the universal statement.

## Evidence

The primary source is the URL in the frontmatter, with Problem 9.2 at
`S9.Thmtheorem2`, Definition 2.1 at `S2.Thmtheorem1`, and the quaternion
formula at `S2.Thmtheorem4` / `S2.E4`. The retrieved source has SHA-256
`6a88fafa1415222c40d99f2e9b3803136c7c58883cb8f04af3012a33340ddb59`.
The Library note is `Library/QuadraticForms/mehat2026eulermagic.md`.

The formal source is `D5/S3/Arith/Mehat/OrthogonalityProducts.lean`, with
its canonical Blueprint Scribe and the source-bound registration at
`Reg/D5/S3/Arith/Mehat/OrthogonalityProducts.lean`. The theorem's standard
axiom boundary is `Classical.choice`, `Quot.sound`, and `propext`; no new
axiom is introduced. The finite entry certificate supports the polynomial
argument and unrestricted induction; it supplies no coefficient-size or
computational-complexity estimate.

## Triage

This is a tier-1 external named problem, with `triage: theorem`; the target
is the complete original positive-length Problem 9.2. The repository proof
uses the classical quaternion formula and a simultaneous polynomial-avoidance
construction. The formula itself is not new mathematics.

Proved: the full factor-existence and indexed-product separation assertion.
The stronger auxiliary invariant of nonzero individual entries is maintained
by `factors_all`; the public theorem does not require it as a premise.
The decisive structure is pairwise zero/nonzero separation of entry
polynomials, which permits every finite collision family to be avoided at
one common integer tuple.

Unresolved here: entry-size bounds, an efficient extraction algorithm, and
any additional Euler diagonal requirements. The paper's transfer from
orthogonality factors to complete Euler magic matrices requires its own
same-matrix diagonal argument. Neither Problem 9.1 nor Problem 9.3 is
claimed as a consequence in this unit. Generalizations of the polynomial
avoidance method require separate statements and verification.

## ASSUMED-UNVERIFIED

No unverified mathematical premise is added to the stated theorem. Exhaustive
literature coverage and worldwide priority are unverified because the
bounded source check does not cover all citing and related literature.
The registration link does not certify literature completeness. The source
correspondence and the external open-status claim remain distinct from Lean
kernel validity.
