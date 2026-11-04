---
slug: fiol-martinezmontoya-riosfukelman-2020-tree-lee-yang
bibkey: fiolmartinezmontoyariosfukelman2020quiver
doi: 10.1007/JHEP08(2020)161
url: https://arxiv.org/abs/2006.06379v2
triage: theorem
motivation_gids:
  - D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.result
  - D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.result
---

# Positive joint weights and all-vertex physical weights in the tree Lee–Yang conjecture

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

### Statement echo

The public definitions are `splits`, `mass`, `treePoly` and `claim`.
The tree condition is the frozen
`D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport.NamedSpanningTree`
with `Set.univ`, selecting every edge: its nonloop, distinct and isTree fields
state exactly the finite-type tree convention. The subtype of all edges is
in bijection with the edge type, so its injectivity and support conditions
are the same as the source convention.
## Motivation

The settling declaration is
`D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation.result`.
Its admission basis is `open-problem-resolution (#15357; Refuted)`;
[the preregistration](https://github.com/the-omega-institute/trureturing/issues/15357)
fixes the source statement and the finite-type encoding.

The only public theorem is `result : ¬ claim`.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).

## Gap

The preregistration records a screen of 29 INSPIRE citing works, attributed
to its search producer, with no settlement of Conjecture 1 found. This is
`not-found-in-searched-scope`, not an exhaustive novelty claim.
The fixed-configuration Lee–Yang theorem and the one-edge result do not
assert closure under arbitrary positive mixing of different vertex masses.
The exact all-vertex physical claim at issue #17677 is now separately refuted
by the kernel-checked nine-vertex/eight-edge all-total-three result below; the
older arbitrary-joint-weight settlement does not supply that implication.


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
The Scribe is designed to record one `OpenProblemResolutionClaim`, `Refuted`,
on the existing `result`, with
`D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.result` as its supported
`additionalMembers`. The authorized Mac `deposit-uncovered` run completed
with exit 0 and `PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED`, with `reason=NO_ATOM`;
it added the module to
`Golden/Frozen/state/D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.lean.json`.
The deposited `statement_id` is
`sha256:e4a7de999321ecb7471bcc989fe84a2733afd351a1caa39ac4131053095b1e5f`,
and the current delivery scoped report is
`sha256:502415af958772b8c0adff34accb8ed232d6b3426572bc93db96c8fbd462e557`.
No duplicate claim is emitted; the native axiom closure remains bounded by
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The positive-sequence and physical boundary arguments under Triage are prose, with reciprocal completion attributed to Lalín–Smyth Theorem 1. Their corresponding unpublished source has reported Lean 4.33 compilation evidence, but no accepted current native exact-type/axiom report. The new physical e8 result is the separate current kernel-checked settlement; it does not turn those prose families into Lean theorems.

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

### All-vertex physical e8 settlement

The canonical resolution claim remains the single claim for this dossier. Its
existing arbitrary-joint-weight result is joined by the additional member
`D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.result`, whose source is
`D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.lean`. The physical result uses
`admission_basis: open-problem-resolution` under preregistration [#17677](https://github.com/the-omega-institute/trureturing/issues/17677),
which records the published Fiol--Martínez-Montoya--Rios Fukelman statement,
complete quantifiers, the all-vertex (2.19) reading and a bounded literature
screen before the probe. Its Scribe member is emitted through the existing
`QuiverTreeIsingRefutation` document with `additionalMembers`; no duplicate
problem slug or second resolution claim is introduced. Final freeze membership
and the emitted current report are established only by the authorized deposit
run below.

The refutation is literal for the registered all-vertex physical proposition:
vertices `Fin 9 = c,u,v,u1,u2,u3,v1,v2,v3`, edges
`cu,cv,uu1,uu2,uu3,vv1,vv2,vv3`, all eight totals equal to three, and
`tau = -1`. The proof keeps all 256 complementary splits and all 512 spins
per split, retains the nine actual vertex factors, proves the exact
`360^8*36/512` normalization, and uses the reciprocal/nonreal-root certificate
to produce a root inside and its reciprocal outside the unit circle. The exact
Lean result is a closed `Not claim` with axiom closure contained in
`propext`, `Classical.choice`, and `Quot.sound`; its public declaration is a
designated `refutes` utility result. The readable automorphism count
`|Aut(T)| = 72` and source prefactor `120^8/4` remain correspondence prose,
not separate kernel theorems.

The physical settlement is scoped to the all-vertex (2.19) construction and
this exact witness. It preserves the printed shorter (2.31) expression as a
distinct source reading and asserts no author-approved erratum or intent. It
does not settle arbitrary other total multisets, other trees, other tau, the
full tree ensemble, Conjecture 2, the all-tau family, or priority. The existing
assignment-summed m60 coefficient exposition remains a separate complete
source-assessed calculation; it is not silently promoted to the Lean result or
used to weaken the fixed-labelled claim.


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
- **Physical boundary family, proved in prose below.** At $\tau=-1$,
  every fixed labelled two-edge pair $a,b\ge2$ with $\min(a,b)=2$ is
  covered using all three physical vertex factors. This is separate from
  the kernel-checked arbitrary-weight refutation and from the experiment.
- **All-vertex physical e8 result, kernel-checked.** The separate
  `QuiverTreePhysicalE8.result` refutes the exact all-vertex physical claim at
  the explicit nine-vertex/eight-edge all-total-three witness. It is grouped
  with the existing resolution through `additionalMembers`, while preserving
  the arbitrary-joint-weight result and its different witness.
- **Residual physical-weight questions, open.** Other fixed total multisets,
  other trees, both two-edge totals at least three, the full tree family with
  the binomial and all-vertex factors of (2.31), the all-τ variant, and the
  general assignment-summed family remain open. The experiment entry has no
  physical-weight reading.
- **Consequences for the source, source reading.** Its fixed-configuration
  result and its one-edge theorem remain outside the refutation. The
  physical planar-free-energy specialization requires its own restricted
  argument; the arbitrary-joint-weight conjecture cannot supply it.
  Conjecture 2 concerns a sum over trees and is not settled by this instance.

### Physical two-edge boundary family, proved in prose

For all fixed labelled totals $a,b\ge2$ with $\min(a,b)=2$, the physical
two-edge polynomial at $\tau=-1$, including both leaf factors and the
central vertex factor, has all its complex roots on the unit circle.
We first give the positive-sequence argument that supplies its
root-location step, then identify the actual weights, incidence, masses
and state sum. These are prose arguments, using established reciprocal
completion, with no literature-priority claim.

**Positive-sequence polynomial.** Let $b\ge2$ and let $v_\ell>0$ for every
$1\le\ell\le b-1$, without any symmetry assumption. Define

$$
P_{b,v}(X)=(1-X)\sum_{\ell=1}^{b-1}
v_\ell(1-X^\ell)(1+X^{b+1-\ell}),\qquad
h(X)=\sum_{\ell=1}^{b-1}v_\ell\sum_{j=0}^{\ell-1}X^j.
$$

The seed has real coefficients, degree $d\le b-2$, and
$h(0)=\sum_\ell v_\ell>0$. The geometric-sum identity gives

$$
(1-z)h(z)=\sum_\ell v_\ell-\sum_\ell v_\ell z^\ell.
$$

For $|z|<1$, the interval of indices is nonempty and each $\ell\ge1$, so

$$
\left|\sum_\ell v_\ell z^\ell\right|
\le\sum_\ell v_\ell|z|^\ell<\sum_\ell v_\ell.
$$

Thus $h$ has no zero in the open unit disk. The conclusion depends on this
strict bound and the completion identity below; positivity of a mixture
alone would not locate its roots.

The reciprocal-completion result used here is the real special case of
M. N. Lalín and C. J. Smyth, *Unimodularity of zeros of self-inversive
polynomials*, [arXiv:1201.0774v1](https://arxiv.org/abs/1201.0774v1),
Theorem 1, page 3, equation (5)
([DOI 10.1007/s10474-012-0225-4](https://doi.org/10.1007/s10474-012-0225-4)).
Its exact forward statement takes a nonzero complex polynomial $g$ of
degree $n$ whose zeros lie in the closed unit disk, an integer $D>n$,
and $|\lambda|=1$. It puts every zero of
$z^{D-n}g(z)+\lambda g^*(z)$ on the unit circle, where

$$
g^*(z)=z^n\overline{g(1/\bar z)}
$$

is understood as a polynomial. To match the present hypotheses, set
$g(z)=z^d h(1/z)$. Since $h(0)\ne0$, this is a nonzero polynomial of
degree $d$; its zeros are the reciprocals of those of $h$, hence are in
the closed disk. Its coefficients are real and $g^*=h$. Taking
$D=b>d$ and $\lambda=1$ yields the completion
$F(z)=h(z)+z^b h(1/z)$. Constants and zeros on the boundary are allowed
by the cited theorem.

Here is the corresponding direct argument, including the root-multiplicity
step. Factor $h(z)=c\prod_{j=1}^d(z-\alpha_j)$ over $\mathbb C$, listing
roots with multiplicity. Disk stability gives $|\alpha_j|\ge1$.
For $|z|\le1$,

$$
|\bar z-\alpha_j|^2-|1-\alpha_j z|^2
=(|\alpha_j|^2-1)(1-|z|^2)\ge0.
$$

When $z\ne0$, use
$|z|\,|z^{-1}-\alpha_j|=|1-\alpha_j z|$, multiply the nonnegative
factor inequalities, and include $|c|$. Real coefficients give
$|h(\bar z)|=|h(z)|$, so

$$
|z|^d|h(1/z)|\le|h(z)|.
$$

The empty product covers a constant seed. Since $d<b$,
$z^b h(1/z)$ extends to a polynomial with zero constant coefficient.
Thus $F(0)=h(0)\ne0$. If $F(z)=0$ with $0<|z|<1$, the preceding
comparison would give

$$
0<|h(z)|=|z|^b|h(1/z)|
\le|z|^{b-d}|h(z)|<|h(z)|,
$$

a contradiction. For $z\ne0$, the identity
$F(1/z)=z^{-b}F(z)$ transports any root outside the disk to one
inside it. Therefore every root of $F$ has modulus one; no
distinct-root assumption has been used.

To connect $F$ to the stated positive-sequence polynomial, the forward
and inverse geometric sums give, for each $\ell$ and $z\ne0$,

$$
\begin{aligned}
(1-z)^2\left(\sum_{j=0}^{\ell-1}z^j
+z^b\sum_{j=0}^{\ell-1}z^{-j}\right)
&=(1-z)\bigl((1-z^\ell)-z^{b+1}(1-z^{-\ell})\bigr)\\
&=(1-z)(1-z^\ell)(1+z^{b+1-\ell}).
\end{aligned}
$$

The last equality uses $z^{b+1}z^{-\ell}=z^{b+1-\ell}$.
Multiply by $v_\ell$ and sum to obtain the polynomial identity

$$
P_{b,v}(z)=(1-z)^2F(z).
$$

At zero both sides are $\sum_\ell v_\ell>0$, so the inverse notation
introduces no exceptional root. The root $z=1$ is already on the
circle; every other root is a root of $F$. This proves the full
positive-sequence statement, including asymmetric coefficients and
repeated roots. At $b=2$, the seed is the positive constant $v_1$,
and the same argument applies with $d=0$.

**All-vertex physical weights.** In the notation of the source's
equation (2.15), for positive integer endpoint parts define

$$
f(t)=\frac{(2t)!}{(t-1)!\,t!},\qquad
\mathcal V(t_1,\ldots,t_\alpha)
=\frac{(m-1)!}{(m-\alpha+2)!}\prod_{j=1}^{\alpha}f(t_j),
\quad m=\sum_j t_j.
$$

These are real factorial ratios. Every endpoint part is at least one,
so $m\ge\alpha$ and the factorial arguments are nonnegative.
The all-vertex reading of (2.31) is used: its printed vertex-product
upper limit is $m$ for $m$ edges, whereas the explicit construction
after (2.15) and the products in (2.16)–(2.19) attach factors to all
$m+1$ vertices. This is an editorial reading of the source, not a
claim of a published erratum.

Use the native incidence $0\to1\leftarrow2$, with source list $(0,2)$
and target list $(1,1)$. For totals $(a,b)$ and split $(k,\ell)$, the
native mass definition assigns $k,\ell$ to the leaves and
$a-k,b-\ell$ to the centre. The physical weight is therefore exactly

$$
W_{a,b}(k,\ell)=
\binom{2a}{2k}\binom{2b}{2\ell}
\mathcal V(k)\mathcal V(a-k,b-\ell)\mathcal V(\ell).
$$

It includes all three vertex factors. The paper's arrow convention
puts $n_i-k_i$ at the origin and $k_i$ at the end; the identical
endpoint assignment is represented there by reversing both native
arrows. No split complement at a fixed incidence is assumed to
preserve the polynomial.

For totals $(2,b)$ the native split set is exactly
$(k,\ell)=(1,\ell)$ with $1\le\ell\le b-1$. On this whole interval,

$$
\mathcal V(1)=1,\qquad
\mathcal V(\ell)=\frac{f(\ell)}{\ell(\ell+1)},\qquad
\mathcal V(1,b-\ell)=\frac{2f(b-\ell)}{b+1-\ell}.
$$

The required edge cancellation, with no scalar omitted, is

$$
\binom{2b}{2\ell}\frac{f(\ell)f(b-\ell)}{\ell(\ell+1)}
=\binom{2b}{b}\binom b\ell\binom b{\ell+1}.
$$

Indeed, after cancelling $(2\ell)!$ and $(2b-2\ell)!$, the left
side has numerator $(2b)!$ and denominator
$(\ell-1)!\,\ell!\,(b-\ell-1)!\,(b-\ell)!\,\ell(\ell+1)$.
Using $\ell!=\ell(\ell-1)!$ and
$(\ell+1)!=(\ell+1)\ell!$ changes that denominator to
$\ell!(\ell+1)!(b-\ell)!(b-\ell-1)!$, which is also the denominator
of the product of the three binomial coefficients on the right.
All cancelled denominators are nonzero, including when a factorial
argument is zero. The first edge supplies $\binom42=6$, and the
central vertex supplies the remaining factor $2$. Hence

$$
W_{2,b}(1,\ell)=
v_\ell=\frac{12\binom{2b}{b}\binom b\ell\binom b{\ell+1}}{b+1-\ell}>0.
$$

Here $\ell+1\le b$ makes both smaller binomial coefficients positive
and $b+1-\ell\ge2$. All subtractions agree with ordinary integer
subtraction on these actual splits.

**Native state and mass identity.** Write the masses of the three
vertices as $(r,s,t)$. For up-spin indicators
$(u_0,u_1,u_2)\in\{0,1\}^3$, the parity of the number of
opposite-spin edges is $u_0+u_2$ modulo two: each centre indicator
occurs twice. Thus at $\tau=-1$ the actual eight-state sum is

$$
\begin{aligned}
\sum_{u\in\{0,1\}^3}(-1)^{e_\pm(u)}
X^{u_0r+u_1s+u_2t}
&=1-X^r+X^s-X^t-X^{r+s}+X^{r+t}-X^{s+t}+X^{r+s+t}\\
&=(1-X^r)(1+X^s)(1-X^t).
\end{aligned}
$$

For the boundary split $(1,\ell)$ the native mass definition gives
$(r,s,t)=(1,b+1-\ell,\ell)$. The map
$\ell\mapsto(1,\ell)$ is a bijection from
$\{1,\ldots,b-1\}$ to the native split set: the total-two edge
forces its split to be one, and the second coordinate recovers
$\ell$. Reindexing the split sum in the existing treePoly definition,
using the exact weight cancellation and the eight-state identity, gives

$$
\begin{aligned}
P^{\mathrm{ph}}_{(2,b)}(-1,X)
&=\sum_{\ell=1}^{b-1}W_{2,b}(1,\ell)
(1-X)(1+X^{b+1-\ell})(1-X^\ell)\\
&=P_{b,v}(X).
\end{aligned}
$$

This is equality with the actual physical polynomial, with no residual
normalizing scalar. The positive-sequence argument therefore applies.
For totals $(a,2)$, the native splits are $(\ell,1)$. Exchanging
leaves $0$ and $2$ exchanges the edge factors and the two leaf factors,
while $\mathcal V(a-\ell,1)=\mathcal V(1,a-\ell)$ leaves the centre
factor unchanged. The masses become $(\ell,a+1-\ell,1)$ and
commutativity of the three state factors gives the same
$P_{a,v}$. Since $a,b\ge2$ and $\min(a,b)=2$ imply $a=2$ or $b=2$,
both orientations of the labelled total pair are covered, including
$(2,2)$. No sum over assignments of totals to edges has been substituted.

The physical weights on general trees are not subsumed by an edgewise
product model. Writing a vertex factor as
$c(m,\alpha)\prod_j f(t_j)$, its residual factor is
$c(m,\alpha)=(m-1)!/(m-\alpha+2)!$. Vertex degrees one and three
give a sufficient structural product subclass:
$c(m,1)=1/(m(m+1))$ and $c(m,3)=1$, so these factors group by edge.
This is not a necessary condition for factorization at a fixed
assignment; for example, all totals equal to two give singleton split
support. A degree-two centre generally contributes the joint factor
$1/m$, and the boundary proof above uses its exact value rather than
a general positive-mixture principle.

The physical two-edge case with both totals at least three, the full
physical-tree and all-stars families, the all-$\tau$ variant, general sums over
edge assignments or total multisets, Conjecture 2's sum over trees, and
the conditional Wilson-loop assertions remain open. Neither the
general product-weight question nor these residuals follow from the
boundary argument or from the arbitrary-joint-weight refutation.

### Uniform raw split real-stability obstruction

[Full argument, assumptions and unresolved boundaries](../Library/StatisticalMechanics/fiolmartinezmontoyariosfukelman2020quiver.md#lee-yang-split).

### One fixed tree's assignment-summed formal coefficient

[Full argument, assumptions and unresolved boundaries](../Library/StatisticalMechanics/fiolmartinezmontoyariosfukelman2020quiver.md#lee-yang-coefficient).

## ASSUMED-UNVERIFIED

The preregistration's search producer reports its forward-citation screen;
worldwide priority is unverified. Kernel checking establishes the encoded
statements and axiom boundaries, while correspondence to the source requires
the stated finite-type and parameter conventions. The positive-sequence and
physical $\min(a,b)=2$ statements are complete prose arguments, not newly
kernel-checked public theorems. Product-weight questions and physical-weight
generalizations outside the exact all-total-three e8 witness remain open,
including other multisets, other trees and stars, all-$\tau$ and general
edge-assignment sums, Conjecture 2 and conditional Wilson-loop claims; the
numerical product-weight trials do not prove these extensions.

The fixed 123-vertex tree coefficient above has a complete independently checked analytical root proof and remains separate prose evidence. The fixed-labelled all-total-three physical candidate has passed the independent prefreeze review under issue #17677 and now has the deposited state pin recorded above; the broader assignment-summed physical conjecture and all residual families remain open.
