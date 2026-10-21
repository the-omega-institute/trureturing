---
bibkey: chervonyi2025alphageometry2
authors: Yuri Chervonyi; Trieu H. Trinh; Miroslav Olšák; Xiaomeng Yang; Hoang Nguyen; Marcelo Menegali; Junehyuk Jung; Junsu Kim; Vikas Verma; Quoc V. Le; Thang Luong
year: 2025
title: Gold-medalist Performance in Solving Olympiad Geometry with AlphaGeometry2
doi: null
url: https://arxiv.org/abs/2502.03544
claim: AlphaGeometry2 combines language-model proposals of auxiliary constructions with symbolic deduction and search; its double-point reformulation proves equality of differently constructed points.
strata_touched: []
license: citation-only
triage: anchor
---

# Auxiliary constructions as discrete programs

The [primary text, version 3](https://arxiv.org/html/2502.03544v3), §3.1
and Figure 1 describe constructing $X'\in a\cap\omega$, proving
$X'\in b$, and identifying it with $X=a\cap b$ under the relevant
nondegeneracy conditions. Section 6.2 describes the language model proposing
auxiliary constructions and the DDAR symbolic engine deriving facts and
checking the goal. This supports that concrete neuro-symbolic interface;
it does not establish a uniform success-probability or complexity bound
for arbitrary proofs. The elementary semantic and geometric arguments
below are explanatory calculations, not attributed as new results of AG2.

## 1. Conservative constructions

Let $\Gamma(\xi)$ describe the original admissible configurations, and
let an auxiliary object $z$ satisfy $R(\xi,z)$. If
$\Gamma(\xi)\Rightarrow\exists z\,R(\xi,z)$ in every such configuration,
then for any goal involving only the original objects,

$$
\Gamma\models\varphi\quad\Longleftrightarrow\quad
\Gamma\land R\models\varphi.
$$

The forward implication restricts models. For the reverse, extend each
original configuration by one permitted $z$ and apply the expanded
entailment. This is semantic conservativity, not a guarantee that a
particular proof calculus finds a short derivation. Nonparallel lines
permit an intersection; a nondegenerate triangle permits its circumcenter.
Otherwise the construction needs another definition or a separate branch.
Naming such an object can expose useful relations without supplying new
empirical facts. Proposal generation, actual construction, legality checks
and proof completion all contribute to its cost.

## 2. Why the circumcenter simplifies the Euler relation

For noncollinear $A,B,C$, let $O,G,H$ be the circumcenter, centroid and
orthocenter in the Euclidean plane. Write $a=A-O$, $b=B-O$, $c=C-O$;
then their norms are equal. The vector $h=a+b+c$ satisfies

$$
(h-a)\cdot(b-c)=(b+c)\cdot(b-c)=\|b\|^2-\|c\|^2=0.
$$

Cyclically, $O+h$ lies on all three altitudes, so $H-O=a+b+c$.
Since $G-O=(a+b+c)/3$, this proves $H-O=3(G-O)$, including coincident
centers. When $O\ne G$, the Euler line and $GH=2OG$ follow. The choice
of origin turns equal distances into cancellation of squared norms.
Matching a perpendicularity goal to a zero dot product, then to an
equal-norm construction, describes a checkable proposal mechanism; it
does not require that every successful proposal arise this way.

The candidate “construct the circumcenter” is a discrete program. An
absolutely continuous random point in the plane has probability zero of
hitting a specified point exactly. A distribution on construction programs
can instead give that exact construction positive mass, subject to its
legality and implementation. Experience influences which programs are
proposed; success is still measured by actual certificate verification.

## 3. Bounded construction depth

With at most $B$ fixed templates of arity at most $r$, at most $c$ new
objects per step, initially at most $n$ objects, and at most $d$ steps,
the number of syntactic candidate sequences is bounded by

$$
\sum_{j=0}^d\bigl[B\max\{1,n+cd\}^r\bigr]^j.
$$

Each step chooses a template and a tuple of existing objects; multiply
this common upper bound over steps and sum over lengths. The maximum
also covers nullary templates when there are no objects; each has one
empty tuple. Fixed $B,r,c,d$ give polynomial
enumeration if representations, construction, legality checking and the
specified bounded proof procedure also have uniform polynomial cost.
Failure means no certificate was found within that grammar and budget;
it does not imply that the original statement is false.
