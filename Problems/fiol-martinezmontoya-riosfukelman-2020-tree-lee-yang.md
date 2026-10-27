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

The physical specialization has a uniform obstruction to one tempting
intermediate route. This is a statement about the raw split generating
polynomial, not about the Lee--Yang state sum. Keep $a,b\ge3$ fixed, put
$N=a+b$, and use the leaf-oriented incidence $0\to1\leftarrow2$ (equivalently,
reverse both printed arrows when reading the source convention). Set

$$
f(t)=\frac{(2t)!}{(t-1)!\,t!},\qquad
U_n(j)=\binom nj\binom n{j+1}.
$$

The source's (2.15) gives
$\mathcal V(t_1,\ldots,t_\alpha)=\frac{(d-1)!}{(d-\alpha+2)!}
\prod_i f(t_i)$, where $d=\sum_i t_i$. Thus the two leaves contribute
$f(k)/(k(k+1))$ and $f(\ell)/(\ell(\ell+1))$, while the degree-two
centre contributes $f(a-k)f(b-\ell)/(N-k-\ell)$. Including all three
vertex factors, as required by the physical product in (2.31), gives

$$
\rho_{k\ell}=\binom{2a}{2k}\binom{2b}{2\ell}
 \frac{f(k)}{k(k+1)}
 \frac{f(a-k)f(b-\ell)}{N-k-\ell}
 \frac{f(\ell)}{\ell(\ell+1)}.
$$

For every $1\le j<n$ the factorial cancellation is exact:

$$
\binom{2n}{2j}\frac{f(j)f(n-j)}{j(j+1)}
 =\binom{2n}{n}\binom nj\binom n{j+1}.
$$

Indeed, after cancelling $(2j)!$ and $(2n-2j)!$, use
$j!=j(j-1)!$ and $(j+1)!=(j+1)j!$; every factorial argument is
nonnegative on the displayed split range. Consequently

$$
\rho_{k\ell}=C_{ab}\,w_{k\ell},\qquad
C_{ab}=\binom{2a}{a}\binom{2b}{b}>0,\qquad
w_{k\ell}=\frac{U_a(k)U_b(\ell)}{N-k-\ell}.
$$

This is the source echo and scalar bridge; it does not replace the state
sum in (2.30). Define only the raw split polynomial

$$
K_{a,b}(u,v)=\sum_{k=1}^{a-1}\sum_{\ell=1}^{b-1}
 w_{k\ell}u^{k-1}v^{\ell-1}.
$$

At $\tau=-1$, the eight-state sum for a fixed split is
$(1-X^k)(1+X^{N-k-\ell})(1-X^\ell)$, so the physical polynomial is

$$
P^{\mathrm{ph}}_{a,b}(-1,X)=C_{ab}\sum_{k=1}^{a-1}\sum_{\ell=1}^{b-1}
w_{k\ell}(1-X^k)(1+X^{N-k-\ell})(1-X^\ell).
$$

The following calculation concerns $K_{a,b}$ only.

It has bidegree $(a-2,b-2)$. Apply
$\partial_u^{a-3}\partial_v^{b-3}$. Only
$k\in\{a-2,a-1\}$ and $\ell\in\{b-2,b-1\}$ survive. Writing

$$
A_n=U_n(n-2)=\frac{n^2(n-1)}2,\qquad B_n=U_n(n-1)=n,
$$

the four undifferentiated corner coefficients are

$$
\begin{pmatrix}
A_aA_b/4 & A_aB_b/3\\[2pt]
B_aA_b/3 & B_aB_b/2
\end{pmatrix};
$$

the denominators $4,3,3,2$ are respectively
$N-(a-2)-(b-2)$, $N-(a-2)-(b-1)$,
$N-(a-1)-(b-2)$, and $N-(a-1)-(b-1)$. Including the derivative
factors and dividing by the positive scalar
$(a-3)!(b-3)!A_aA_b/4$ gives exactly

$$
1+c_a u+c_b v+\frac98c_ac_buv,
\qquad
c_a=\frac{8(a-2)}{3a(a-1)},\quad
c_b=\frac{8(b-2)}{3b(b-1)}.
$$

Both $c_a$ and $c_b$ are strictly positive, including the corner case
$a=b=3$ (where no differentiation is taken). This calculation checks the
degree, all four central denominators, and every factorial scalar.

The closure step uses Borcea--Brändén--Liggett, *Negative Dependence and
the Geometry of Polynomials*, [arXiv:0707.2340](https://ar5iv.labs.arxiv.org/html/0707.2340), Proposition 3.1(2): a
partial derivative of a real-stable polynomial is real-stable or zero,
and positive coordinate scaling preserves real stability. The derivative
above is nonzero because its $uv$ coefficient is positive. After the
positive rescaling $x=c_au$, $y=c_bv$, a real-stable $K_{a,b}$ would force

$$
G(x,y)=1+x+y+\frac98xy
$$

to be real-stable. But the exact bilinear zero

$$
x=i,\qquad
y=-\frac{1+i}{1+9i/8}=-\frac{136}{145}+\frac{8}{145}i
$$

has both coordinates in the open upper half-plane and satisfies
$G(x,y)=0$. Thus $G$, the differentiated polynomial, and $K_{a,b}$ are
all non-stable. Multiplication by the positive physical scalar $C_{ab}$
does not change this conclusion. The same paper's Theorem 4.1 gives the
corresponding bilinear real-stability criterion; the displayed zero is a
direct witness, so no sign convention from that criterion is being used
implicitly here.

The mechanism is the degree-two central factor. In a $2\times2$ corner,
dividing the stable product coefficients by the successive central
degrees produces $1/M,1/(M-1),1/(M-1),1/(M-2)$, whose bilinear minor is

$$
\frac1{(M-1)^2}-\frac1{M(M-2)}
=-\frac1{M(M-2)(M-1)^2}<0\qquad(M\ge4).
$$

This rules out the raw split-real-stability lemma as a route for every
interior pair $a,b\ge3$. It does not produce a zero of
$P^{\mathrm{ph}}_{a,b}(-1,X)$ off the unit circle: that polynomial still
contains the three spin factors from (2.30); the scalar bridge only
relates the weights without identifying the two zero sets. The physical
two-edge Lee--Yang question for $a,b\ge3$, the full tree problem, other
$\tau$, general assignment sums, and Conjecture 2 therefore remain open. This is
source-grounded prose only, with no new Lean declaration, kernel claim,
or literature-priority assertion; alternative disk-specific or
interlacing routes remain available.

### One fixed tree's assignment-summed formal coefficient

The following is a complete analytical calculation at $\tau=-1$, assessed
directly against the source and checked independently by hand. It is not a
new Lean theorem. The inherited frozen `QuiverTreeIsingRefutation.result`
concerns arbitrary positive joint split weights on a different, three-vertex
example. Its kernel verification does not extend to the calculation below.

Let $T$ have a unique degree-two centre $c$, two hubs $h_1,h_2$ adjacent to
$c$, and sixty leaves adjacent to each hub. Each hub has degree $61$;
$T$ has $123$ vertices, $122$ edges and $122$ odd-degree vertices. Replace
each occurrence of $\zeta(2n-1)$ in (2.19) by an independent commuting
formal generator $Z_{2n-1}$. Write $F_{0,T}$ for only this fixed unlabelled
tree's summand in (2.19). No algebraic independence of numerical odd zeta
values is assumed. The coefficient considered here assigns total three to
two edges and total two to the other $120$ edges.

For $X=\widetilde\lambda_2/\widetilde\lambda_1$ with
$\widetilde\lambda_1\ne0$, the result is

$$
[Z_5^2 Z_3^{120}]F_{0,T}
=200\,12^{120}\widetilde\lambda_1^{246}(1-X)^{122}Q(X),
$$

where, with $S_r=\sum_{j=0}^{r-1}X^j$,
$U=S_{61}$, $V=S_{62}$, $W=S_{63}$, $L=1+X$ and $H_r=1+X^r$,

$$
\begin{aligned}
Q={}&H_2(27691682V^2+20763180UW+1771440LUV+14280L^2U^2)\\
&+H_3(59048UV+960LU^2)+9H_4U^2.
\end{aligned}
$$

The polynomial $Q$ has degree $124$ and $124$ distinct simple roots, all on
the unit circle and none equal to $1$ or $-1$. Thus
$P=(1-X)^{122}Q$ has degree $246$, with $125$ distinct roots: $1$ has
multiplicity exactly $122$, and the other $124$ roots are simple. Its
constant and leading coefficients are both $50300599$. Homogenization
therefore adds no projective root at infinity, and zero is not a root.
These statements concern this one tree's contribution, this formal
monomial and this parameter; other trees also contribute to the same
formal coefficient of the full free energy.

**Source convention and interpretation.** Equation (2.19) explicitly
includes all $m+1$ vertices of an $m$-edge tree. Its vertex correlator is

$$
\mathcal V(t_1,\ldots,t_d)
=\frac{(M-1)!}{(M-d+2)!}\prod_j f(t_j),\qquad
f(t)=\frac{(2t)!}{(t-1)!t!},\qquad M=\sum_jt_j.
$$

The modified factor is
$\mathcal V(\widetilde\lambda_1^M+(-1)^d\widetilde\lambda_2^M)$.
Identifying this calculation with the Ising weight displayed in (2.31)
uses the editorial all-vertex reading: that display prints the upper
vertex-product index $m$, whereas the construction and (2.16)--(2.19)
include $m+1$ factors. No author-approved correction or established
erratum is asserted. The inspected arXiv record lists v2 as the latest
revision, and the inspected INSPIRE and Crossref records display no
related correction; this bounded observation does not determine authorial
intent or exclude a correction elsewhere. Equation numbers here follow
the PDF; the HTML labels are shifted.

The predecessor, Fiol--Martínez-Montoya--Rios Fukelman,
*The planar limit of N=2 superconformal field theories*,
[arXiv:2003.02879v3](https://arxiv.org/abs/2003.02879v3), Section 2.3
around (44)--(46), explains complementary-split orientation invariance
after the split sums and the edge-labelling factor $m!/|\operatorname{Aut}T|$
after the total sums. Individual correlator products before these sums
need not agree. The present assignment sum uses that distinction.

**All assignments and their automorphisms.** An assignment is a
two-element subset $A$ of the $122$ named edges, so there are
$\binom{122}{2}=7381$ assignments. The unique centre forces every
automorphism to interchange or fix the hubs and to permute their leaves;
thus $|\operatorname{Aut}T|=2(60!)^2$. Both selected edges are central,
exactly one is central, or neither is central. In the second case the
pendant lies at the same or opposite hub; in the third case the pendants
lie at the same or opposite hubs. This gives an exhaustive disjoint
partition:

| Placement of the two total-three edges | Multiplicity | Stabilizer order |
| --- | ---: | --- |
| Both central edges | $1$ | $2(60!)^2$ |
| Central edge and same-hub pendant | $2\cdot60=120$ | $60!59!$ |
| Central edge and opposite-hub pendant | $2\cdot60=120$ | $60!59!$ |
| Two same-hub pendants | $2\binom{60}{2}=3540$ | $2\cdot60!58!$ |
| Two opposite-hub pendants | $60^2=3600$ | $2(59!)^2$ |

Their multiplicities sum to $7381$. Each orbit contributes
$|O|/|\operatorname{Aut}T|=1/|\operatorname{Stab}A|$ times its
representative. Equal weighting of the five representatives would be
incorrect. Each ordered tuple of totals with two threes occurs once;
$122!/(2!120!)=7381$ already counts it. There is no additional factorial
or orbit divisor: the source's original $1/m!$ has already cancelled the
edge-labelling factor.

**Exact physical weights and spin sum.** For any up-spin vertex set $B$,
$\sum_{v\in B}\deg v=2|E(B)|+|\partial B|$. Consequently the complete
spin sum at $\tau=-1$ is

$$
\sum_{B\subseteq V(T)}(-1)^{|\partial B|}X^{\sum_{v\in B}M_v}
=\prod_v(1+(-1)^{\deg v}X^{M_v}).
$$

This retains every state and every edge sign. A total-two edge has only
the split $(1,1)$ and contributes $\binom42 f(1)^2=24$, since $f(1)=2$.
A total-three edge has the two endpoint allocations $(1,2),(2,1)$;
each contributes $\binom62 f(1)f(2)=360$, since $f(2)=12$.
Hence each assignment has exactly four allocations, each selected edge
adding one unit to one endpoint, including when that endpoint is a leaf.

Write $M_v=d_v+r_v$. The residual vertex factorial factor and its ratio
to the all-one endpoint baseline are

$$
f_d(r)=\frac{(d+r-1)!}{(r+2)!},\qquad
a_d(0)=1,\quad a_d(1)=\frac d3,\quad
a_d(2)=\frac{d(d+1)}{12}.
$$

Thus $a_2(1)=2/3$, $a_2(2)=1/2$, $a_{61}(1)=61/3$,
$a_{61}(2)=1891/6$ and $a_1(1)=1/3$; a leaf cannot receive two
increments here. The baseline product is $(60!)^2/2^{123}$, and

$$
\frac{(60!)^2}{2^{123}}24^{120}360^2
=16200(60!)^2 12^{120}=18C_0,\qquad
C_0=900(60!)^2 12^{120}.
$$

The endpoint changes are already in the two factors $360$ and must not be
inserted again in $a_d(r)$. Every mass is positive, so the $122$
odd-degree vertices each supply $(1-X)S_{M_v}$. The centre supplies
$H_{2+r_c}$. The factor $(1-X)^{122}$ is common even when a selected
pendant gives a leaf mass two.

After division by $C_0$ the seven allocation weights are: different
hubs, $18(61/3)^2=7442$; centre and hub,
$18(2/3)(61/3)=244$; twice centre, $18(1/2)=9$; twice one hub,
$18(1891/6)=5673$; hub and leaf, $18(61/3)(1/3)=122$; centre and
leaf, $18(2/3)(1/3)=4$; two distinct leaves, $18(1/3)^2=2$.

For each assignment let $P_A$ be the full split- and spin-summed physical
polynomial before the external source factors, and set
$P_A=C_0(1-X)^{122}q_A$. The five orbit polynomials are exactly

$$
\begin{aligned}
q_{CC}={}&7442H_2V^2+488H_3UV+9H_4U^2,\\
q_{CS}={}&5673H_2UW+122H_2LUV+244H_3UV+4H_3LU^2,\\
q_{CO}={}&7442H_2V^2+122H_2LUV+244H_3UV+4H_3LU^2,\\
q_{SS}={}&5673H_2UW+244H_2LUV+2H_2L^2U^2,\\
q_{SO}={}&7442H_2V^2+244H_2LUV+2H_2L^2U^2.
\end{aligned}
$$

For $CC$ the four allocations are the two hubs, centre and hub in two
ways, and twice centre. For $CS$ they are twice the common hub, hub and
leaf, centre and hub, and centre and leaf. For $CO$ they are both hubs,
central-edge hub and opposite leaf, centre and opposite hub, and centre
and leaf. For $SS$ they are twice the common hub, hub and leaf in two
ways, and both leaves. For $SO$ they are both hubs, hub and the other
leaf in two ways, and both leaves. In particular the same-hub double
increment uses $a_{61}(2)$, not $a_{61}(1)^2$.

Now $Q=q_{CC}+120q_{CS}+120q_{CO}+3540q_{SS}+3600q_{SO}$.
Every aggregate multiplier follows from the orbit counts:

$$
\begin{aligned}
[H_2V^2]:&\quad7442(1+120+3600)=27691682,\\
[H_2UW]:&\quad5673(120+3540)=20763180,\\
[H_2LUV]:&\quad122(120+120)+244(3540+3600)=1771440,\\
[H_2L^2U^2]:&\quad2(3540+3600)=14280,\\
[H_3UV]:&\quad488+244(120+120)=59048,\\
[H_3LU^2]:&\quad4(120+120)=960,\\
[H_4U^2]:&\quad9.
\end{aligned}
$$

The bracket labels in this display identify the displayed product terms,
not an assertion that these seven polynomials form an independent basis.

**Source prefactor.** Here $m=122$, $\sum_e n_e=246$ and
$\prod_e n_e=9\cdot2^{120}$. Equation (2.19) supplies

$$
\frac{(-2)^{122}(-1)^{246}}{9\cdot2^{120}|\operatorname{Aut}T|}
=\frac4{9|\operatorname{Aut}T|}.
$$

Multiplication by $C_0$ and $|\operatorname{Aut}T|=2(60!)^2$ gives
exactly $200\,12^{120}$. Also $\sum_v M_v=\sum_e n_e=246$,
so all vertex couplings together supply
$\widetilde\lambda_1^{246}$. This proves the stated homogeneous
coefficient identity, with no omitted scalar or vertex factor.

**Every monomial coefficient.** Put $q_k=[X^k]Q$, with $q_k=0$ outside
$0\le k\le124$. The complete coefficient list is specified by reflection
$q_{124-k}=q_k$ and

$$
\begin{gathered}
q_0=50300599,\qquad q_1=102402158,\qquad q_2=204758579,\\
q_k=104231678k-3720026\quad(3\le k\le60),\\
q_{61}=6331788166,\qquad q_{62}=6354351346.
\end{gathered}
$$

For $k\le60$ each underlying convolution $S_aS_b$ has coefficient $k+1$.
Let $K=27691682+20763180=48454862$. The small factors are $H_2$,
$H_2L=1+X+X^2+X^3$,
$H_2L^2=1+2X+2X^2+2X^3+X^4$, $H_3$,
$H_3L=1+X+X^3+X^4$ and $H_4$. For $3\le k\le60$ their convolution gives

$$
2Kk+1771440(4k-2)+14280(8k-8)+59048(2k-1)
+960(4k-4)+9(2k-2)=104231678k-3720026.
$$

At $k=61$ the finite lengths subtract
$20763180+1771440+2\cdot14280+59048+2\cdot960+2\cdot9=22624166$
from that linear formula; at $k=62$ they subtract
$2\cdot27691682+2\cdot20763180+4\cdot1771440+8\cdot14280+
3\cdot59048+6\cdot960+4\cdot9=104292664$.
The first three coefficients follow by the short initial convolutions;
reflection gives all remaining coefficients. The exact evaluations are
$Q(1)=400163878746$, $Q(-1)=41526378$ and $Q(i)=120034$.
Every coefficient of the degree-$246$ normalized polynomial is consequently

$$
[X^k]P=\sum_{j=0}^{122}(-1)^j\binom{122}{j}q_{k-j}.
$$

This is an exact product identity, not numerical root evidence.

**Complete root proof.** Each $S_r$ is real reciprocal of degree $r-1$,
$L$ of degree one and $H_r$ of degree $r$. Every displayed product term
of $Q$ has degree $124$. Their positive multipliers sum to $50300599$,
so $Q$ is nonzero of exact degree $124$, with that constant and leading
coefficient, and $Q(X)=X^{124}Q(1/X)$. Set

$$
F(\theta)=e^{-62i\theta}Q(e^{i\theta}),\qquad0\le\theta\le\pi.
$$

Reciprocity and real coefficients give
$\overline{F(\theta)}=e^{62i\theta}Q(e^{-i\theta})=F(\theta)$.
Thus $F$ is real and continuous; its zeros correspond exactly to roots
of $Q$ at $e^{i\theta}$.

For $a_j=2\pi j/61$, $1\le j\le30$, put $X=e^{ia_j}$.
Then $X^{61}=1$, $X\ne1$, $U=0$ and $V=1$. Only the first term survives,
and $X^{-62}=X^{-1}$ gives

$$
F(a_j)=27691682(X+X^{-1})=55383364\cos a_j.
$$

This is strictly positive for $j=1,\ldots,15$ and strictly negative for
$j=16,\ldots,30$; none of these points equals $\pi/2$.

For $b_j=\pi j/31$, $1\le j\le31$, put $X=e^{ib_j}$ and
$t=X+X^{-1}=2\cos b_j$. Now $X^{62}=1$, $X\ne1$, $V=0$,
$U=-X^{-1}$, $W=1$ and $X^{-62}=1$. The four surviving contributions are

$$
-20763180t,\qquad14280t(t+2),\qquad960(t^2+t-2),\qquad9(t^2-2),
$$

so $F(b_j)=15249t^2-20733660t-1938$. In particular the $H_3LU^2$
and $H_4U^2$ terms are retained. For $1\le j\le15$, $0<t\le2$, whence

$$
F(b_j)\le(30498-20733660)t-1938<0.
$$

For $16\le j\le31$, monotonicity of cosine gives
$t\le-2\sin(\pi/62)$. Concavity of sine on $[0,\pi/2]$ gives
$\sin u\ge2u/\pi$, hence $t\le-2/31$. The quadratic term is nonnegative,
so

$$
F(b_j)\ge\frac{41467320}{31}-1938
=\frac{41407242}{31}>0.
$$

At $b_{31}=\pi$ the exact value is $F(\pi)=Q(-1)=41526378$.
The extra midpoint is also explicit: at $X=i$, $U=1$,
$V=L=1+i$, $H_2=0$, $H_3=1-i$ and $H_4=2$. Therefore
$Q(i)=2(59048+960)+18=120034$, and $i^{-62}=-1$ gives
$F(\pi/2)=-120034<0$. Finally $F(0)=Q(1)=400163878746>0$.
Use the polynomial $Q$ itself at zero angle, so no denominator $1-X$
creates a singular endpoint.

For $1\le j\le30$,
$b_j<a_j<b_{j+1}$: the second inequality is equivalent to
$62j<61(j+1)$, which holds since $j<61$.
Also $a_{15}=30\pi/61<\pi/2<b_{16}=16\pi/31$. Thus

$$
0,b_1,a_1,\ldots,b_{15},a_{15},\pi/2,
b_{16},a_{16},\ldots,b_{30},a_{30},b_{31}=\pi
$$

is a strictly ordered list of $1+31+30+1=63$ points with strictly
alternating signs. The additional midpoint is essential: the two grids
alone do not provide $62$ sign changes. The intermediate value theorem
gives a root in each of the $62$ disjoint open intervals. Exponentiation
is injective on $(0,\pi)$, so these are $62$ distinct roots of $Q$ in
the open upper semicircle. Real coefficients give $62$ distinct conjugate
roots in the open lower semicircle, disjoint from the first set. A
nonzero degree-$124$ polynomial has at most $124$ distinct complex roots;
these exhaust its degree and each is simple. There is no additional,
off-circle, real-axis or repeated root. The nonzero endpoint evaluations
also directly exclude $1$ and $-1$. Since $Q(1)>0$,
$(1-X)^{122}$ adds exactly a root of multiplicity $122$ at $1$;
the nonzero source scalar changes no roots or multiplicities.

**Different fixed-labelled target and admission boundary.** The original
fixed-labelled physical candidate in
[issue #17677](https://github.com/the-omega-institute/trureturing/issues/17677)
places the two threes on the two central edges. Its exact target is the
universal fixed-assignment assertion `claimPhys`: every finite tree with
at least two edges, every fixed assignment of totals at least two, all
physical factorial factors and $\tau=-1$. Its proposed conclusion is
`result : Not claimPhys`. Its polynomial is
$C_0(1-X)^{122}q_{CC}$, not $C_0(1-X)^{122}Q$.
The four split weights there are $C_0(9,244,244,7442)$.

For completeness, its retained analytical obstruction uses, on $|z|=1$,
$a=1-z^{62}$, $b=1-z^{61}$, $c=\operatorname{Re}z$,
$K=(z+\bar z^2)/2$, $h=7442c$ and $d=9(2c^2-1)$:

$$
\begin{gathered}
(1-z)^2q_{CC}(z)=-2z^{63}E,\quad
E=h|a|^2+488\operatorname{Re}(a\bar bK)+d|b|^2,\\
hE=|ha+244\bar Kb|^2+(hd-244^2|K|^2)|b|^2,\\
hd-244^2|K|^2=7442(2c^3+3c-4)>0\quad(c\ge9/10).
\end{gathered}
$$

A root on this arc would force $a=b=0$ and then $z=1$, excluded by
$q_{CC}(1)=60972306$. If all roots were unit roots, counting them with
multiplicity and setting $v=\sum_r(1-r)^{-1}$,
$w=\sum_r(1-r)^{-2}$ gives $q_{CC}'(1)=q_{CC}(1)v$ and
$q_{CC}''(1)=q_{CC}(1)(v^2-w)$. The exact derivative is
$q_{CC}'(1)=3780282972=62q_{CC}(1)$. The excluded arc and
$\operatorname{Re}((1-r)^{-1}-(1-r)^{-2})=1/(2(1-\operatorname{Re}r))<5$
give the non-strict bound $\operatorname{Re}(v-w)\le620$, using
$\deg q_{CC}\le124$. Hence $\operatorname{Re}w\ge-558$ and
$q_{CC}''(1)\le4402q_{CC}(1)$, contrary to
$q_{CC}''(1)=269676602388$ and
$q_{CC}''(1)-4402q_{CC}(1)=1276511376>0$.
This source-assessed fixed-assignment argument has no new current kernel
theorem of its own. The non-strict multiset bound covers an empty multiset.
An unguarded generic strict variant fails at degree zero; its unused proposed
$n\ge1$, degree-$2n$ correction is not an accepted general theorem. The exact
universal physical claim is settled separately by the all-total-three e8 Lean
result above; this m60 calculation remains prose and does not change that
result's admission or scope.

Identifying the preregistered fixed-labelled assertion with a tree's
assignment-summed contribution in the source prose is a separate question.
The positive coefficient example and its analytical proof supply no new
admission basis and do not settle the source's general assignment-summed
physical conjecture. The earlier bind-only disposition for the two-edge
boundary formalization is unchanged. This m60 exposition supplies no new
declaration, proof-shape classification, escape witness, registration, freeze
or open-problem-resolution admission.

The fixed-labelled obstruction and the positive aggregate are compatible
because they concern different polynomials. One placement is not the whole
formal coefficient, and a positive aggregate does not establish the universal
fixed-labelled assertion for this 123-vertex calculation. Other multisets,
other trees, other $\tau$, the full coupling series, sums over trees
(Conjecture 2) and the conditional Wilson-loop questions remain unresolved
here. The general assignment-summed physical tree conjecture remains open; no
literature-priority or broader universal-conjecture resolution is claimed.

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
