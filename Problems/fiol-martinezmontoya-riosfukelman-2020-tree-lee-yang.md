---
slug: fiol-martinezmontoya-riosfukelman-2020-tree-lee-yang
bibkey: fiolmartinezmontoyariosfukelman2020quiver
doi: 10.1007/JHEP08(2020)161
url: https://arxiv.org/abs/2006.06379v2
triage: theorem
motivation_gids:
  - D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.result
---

# Positive joint weights and the tree Lee–Yang conjecture

## Problem

B. Fiol, J. Martínez-Montoya and A. Rios Fukelman, *The planar limit of
N=2 superconformal quiver theories*, JHEP 08 (2020) 161,
arXiv:2006.06379v2, Section 2.2, Conjecture 1:

> For any tree with $e$ edges, any fixed positive integers $n_1,\dots,n_e$
> and arbitrary $\rho(k_i,n_i)>0$ the polynomials
> $P(\tau,x,n_1,\dots,n_e)$ have all their $x$ roots on the unit circle.

Equation (2.30) sums over positive edge splits $1\le k_i\le n_i-1$
and all Boolean spin states. The mass at a vertex is the sum of the integers
assigned to its incident endpoints. A state contributes
$\tau^{e_\pm}x^{\sum_{v\text{ up}}m_v}$, where $e_\pm$ counts
opposite-spin edges. The Lee–Yang parameter range is $-1\le\tau\le1$.
The source's one-edge case is proved through the Lakatos–Losonczi criterion.

The source sentence at `quivers_n_2.tex` lines 343–345 makes $\rho$ a
distribution on the whole split configuration. Thus Conjecture 1 permits
an arbitrary positive joint function; it does not impose edgewise factorization.
The physical specialization in (2.31) includes vertex factors $\mathcal V_i$
that depend jointly on the incident splits, as defined at source lines 198–203.

## Motivation

The settling declaration is
`D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.result`.
Its admission basis is `open-problem-resolution (#15357; Refuted)`;
[the preregistration](https://github.com/the-omega-institute/trureturing/issues/15357)
fixes the source statement and the finite-type encoding.

The public definitions are `IsOrientedTree`, `splits`, `mass`, `treePoly`
and `claim`. The only public theorem is `result : ¬ claim`.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).

## Gap

The preregistration records a screen of 29 INSPIRE citing works, attributed
to its search producer, with no settlement of Conjecture 1 found. This is
`not-found-in-searched-scope`, not an exhaustive novelty claim.
The fixed-configuration Lee–Yang theorem and the one-edge result do not
assert closure under arbitrary positive mixing of different vertex masses.

## Route

Use the three-vertex path oriented $0\to1\leftarrow2$, with $n=(4,4)$,
$\tau=-1$ and the positive joint weights

$$W_{31}=\begin{pmatrix}1&1&1\\1&10&1\\1&1&31\end{pmatrix}.$$

Rows and columns are indexed by $k_1,k_2\in\{1,2,3\}$.
The masses are $(k_1,8-k_1-k_2,k_2)$. The same polynomial arises from
$0\to1\to2$ after reversing the second weight index, $k_2\mapsto4-k_2$.

The module's private `path_poly` computes the source polynomial as

$$P_{31}(x)=48-6x+8x^2-62x^3+24x^4-62x^5+8x^6-6x^7+48x^8.$$

Its private `sextic_factor` and `lift_root` implement the reciprocal reduction

$$P_{31}(x)=2(x-1)^2x^3q(x+x^{-1}),\qquad
q(y)=24y^3+45y^2-2y-26\quad(x\ne0).$$

The private `q_discr` proves $\operatorname{disc}(q)=-16404$;
`q_not_splits` combines the imported cubic discriminant identity with
nonnegativity of a square. Algebraic closure and descent of splitting give
a nonreal root $w$. A root $x$ of $x^2-wx+1=0$ is nonzero and lifts to
$P_{31}(x)=0$. If $|x|=1$, then $x^{-1}=\bar x$ and $w=x+\bar x$ would be
real, a contradiction. This is the kernel-checked route at $M=31$.

## Falsifier

The encoded claim universally quantifies finite vertex and edge types,
loop-free injective unordered edge lists whose support is a tree,
totals $n_i\ge2$, strictly positive joint weights on every allowed split,
$\tau\in[-1,1]$ and every complex root. The theorem `result` negates that
claim without hypotheses. The restriction $n_i\ge2$ removes the empty-split
zero polynomial; failure within this restriction refutes the source's broader
positive-integer wording.

A transcription mismatch or a failed kernel check of `result` would invalidate
this encoded settlement. Neither product weights nor physical weights are
asserted to be counterexamples here.

## Evidence

The canonical module is
`D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.lean` and its Scribe is
`Blueprint/D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.scribe.cs`.
The source note is
`Library/StatisticalMechanics/fiolmartinezmontoyariosfukelman2020quiver.md`.
The Scribe records exactly one `OpenProblemResolutionClaim`, `Refuted`, on
`result`. Its axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

Experiment entry:
[tree Lee–Yang checks at commit 811abbf954710a5a35374d89403c2ea7ce6913eb](https://github.com/the-omega-institute/trureturing-experiments/tree/811abbf954710a5a35374d89403c2ea7ce6913eb/docs/reports/fiol-martinezmontoya-riosfukelman-2020-tree-lee-yang).
Command within that directory: `python3 check.py`; exit 0; final reading
`bad= 0`; script SHA-256
`68dd6193c60e2ef4bbb8c77bbed37d4faa97ba109587b8c84d6a235e52509571`.
The exact checks cover the symbolic octic, reciprocal reduction,
discriminant polynomial, the certificate identity for $q$, and
$\operatorname{disc}(q)=-16404$. The interior check is exactly
$\tau=-19/20$, $M=60$, including its octic and the negative discriminant
of the reciprocal quartic. Numerical octic root deviations are $0.0193$
at $M=31$, $\tau=-1$, and $0.007899294596530382$ at $M=60$,
$\tau=-19/20$. The product-weight computation samples 2,000 trials on this
same three-vertex path with $n=(4,4)$ and $\tau\in[-1,1]$, and reports a
maximum deviation of $2.26\times10^{-8}$. It does not test the physical
vertex-factor weight family or other tree sizes.

## Triage

Tier 1, externally published named conjecture. Resolution: **Refuted** for
arbitrary positive joint weights by `result`. Every theorem in this module
has `proof_shape: bind-only`; the module asserts no escape witness.

### What the settlement shows

- **Mechanism, kernel-checked at $M=31$.** The private `path_poly` identifies
  the exact octic; `q_discr` and `q_not_splits` supply the negative-discriminant
  obstruction, `exists_nonreal_root` supplies a nonreal root, and `lift_root`
  lifts it off the unit circle. The public `result` refutes the universal claim.
- **Single configurations, proved in prose.** At $\tau=-1$, the state sum
  for a fixed split with masses $(a,b,c)=(k_1,8-k_1-k_2,k_2)$ is
  $(1-x^a)(1+x^b)(1-x^c)$, by multiplying the three factors and comparing
  the eight spin contributions. All three exponents are positive, so each
  zero is a root of unity. Positive mixing across configurations with
  different masses fails to preserve this property. This factorization and
  root-of-unity statement are explanations proved here, not exported Lean
  theorems.
- **Family, proved in prose.** For every real $M\ge31$, give the $(3,3)$
  split weight $M$. Exact expansion gives
  $P_M=(M+17)-6x+(M-23)x^2-2Mx^3+24x^4-2Mx^5+(M-23)x^6-6x^7+(M+17)x^8$
  and $P_M=(1-x)^2x^3Q_M(x+x^{-1})$, where
  $Q_M=(M+17)y^3+(2M+28)y^2+(M-35)y-52$.
  The identity $Q_M=2q+(M-31)y(y+1)^2$ shows $Q_M(y)<0$ for $y\le0$:
  put $z=y+5/4\le5/4$ and use
  $q(y)=24z^2(z-3/4)-27(z+1/27)^2-11/432$.
  For $z\le3/4$ the first term is nonpositive. For $3/4<z\le5/4$,
  it is at most $12z^2$, whereas $27(z+1/27)^2\ge27z^2$.
  Hence $q(y)<0$ in both cases and the added term is nonpositive.
  Every real root of $Q_M$ is therefore positive, but Vieta's sum
  $-(2M+28)/(M+17)<0$ prevents all three roots from being real.
  The quadratic lifting argument above gives an off-circle root for every
  $M\ge31$. This uniform family is proved in prose; Lean verifies only $M=31$.
- **Family identities and interior case, computed.** The experiment entry
  verifies the symbolic identities and the exact interior case
  $\tau=-19/20$, $M=60$. Its numerical deviations have precisely the scope
  recorded in Evidence. No uniform interval of interior parameters is claimed.
- **Interior reciprocal identity, proved in prose.** For the computed octic,
  $400P_{60}(x)=x^4R(x+x^{-1})$ for $x\ne0$, where
  $R(y)=30800y^4-2280y^3-110299y^2-38836y+44462$.
  Expansion gives its coefficients in descending order as
  $(30800,-2280,12901,-45676,8664,-45676,12901,-2280,30800)$,
  exactly those of $400P_{60}$. The computed negative discriminant of $R$
  excludes four real roots: a real-root factorization would express the
  discriminant as a positive leading-coefficient power times squared root
  differences. A nonreal root therefore lifts by the same quadratic
  argument to an off-circle root at this interior parameter. This argument
  is not part of the Lean statement.
- **Product-weight scope, computed.** The experiment entry tests only
  $\rho(k_1,k_2)=u_{k_1}v_{k_2}$ on the three-vertex path, $n=(4,4)$,
  in 2,000 random trials. Their small numerical deviations are evidence
  about those trials, not a proof of a product-weight Lee–Yang theorem.
- **Joint-weight scope, source reading.** The arbitrary-positive-function
  interpretation is the distribution sentence at source lines 343–345.
  Physical weights additionally use vertex factors depending jointly on
  incident splits (lines 198–203), so product weights do not subsume them.
- **Product-weight version, open.** Conjecture 1 for edgewise product
  weights on trees with two or more edges is not settled here.
- **Physical-weight version, open.** Conjecture 1 restricted to the physical
  binomial and vertex factors of (2.31) on trees with two or more edges is
  not settled here and has no numerical reading in the experiment entry.
- **Consequences for the source, source reading.** Its fixed-configuration
  result and its one-edge theorem remain outside the refutation. The
  physical planar-free-energy specialization requires its own restricted
  argument; the arbitrary-joint-weight conjecture cannot supply it.
  Conjecture 2 concerns a sum over trees and is not settled by this instance.

## ASSUMED-UNVERIFIED

The preregistration's search producer reports its forward-citation screen;
worldwide priority is unverified. Kernel checking establishes the encoded
statement and axiom boundary, while correspondence to the source requires
the stated finite-type and parameter conventions. Product-weight and
physical-weight generalizations remain open separately; the numerical
product-weight trials do not prove either generalization.
