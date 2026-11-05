---
slug: kaygorodov-martin-gonzalez-viruel-2026-nilpotency-spectrum-conjecture-9
bibkey: kaygorodov2026evolution
doi: 10.48550/arXiv.2610.22248
url: https://arxiv.org/abs/2610.22248v1
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.result
---

# The ordinary nilpotency spectrum of evolution algebras

## Problem

Kaygorodov, Martín González and Viruel, *Evolution algebras: a survey of
results and a list of open problems*, arXiv:2610.22248v1, section 2.3,
Conjecture 9 (Spectrum of nilpotency indices), state:

> Let $\Bbbk$ be an infinite field. An $n$-dimensional nilpotent evolution
> $\Bbbk$-algebra of nilpotency index $k+1$ exists if and only if either
> $k=2^a$ with $0\leq a\leq n-1$, or $k$ has at least two non-zero binary
> digits and $\lfloor\log_2 k\rfloor+s_2(k)\leq n-1$, where $s_2(k)$ is
> the number of non-zero binary digits of $k$.

The whole assertion quantifies over every infinite field $K$, each integer
$n\geq0$ and each integer $k\geq1$. The algebra is a vector space of
dimension $n$ with a $K$-bilinear product and a natural basis satisfying
$e_i e_j=0$ for distinct indices. No associativity, power-associativity,
unit, nondegeneracy, perfectness, nonzero-square or condition on bases of
lower-power subspaces is imposed. The source's section 1.1 defines the
ordinary lower powers by

$$
 A^1=A,\qquad A^m=\sum_{i=1}^{m-1}A^iA^{m-i}\quad(m\geq2),
$$

where a product of subspaces is the linear span of all pair products and
the sum is a sum of subspaces. Thus every positive split and every
parenthesization is included. Index $k+1$ means $A^{k+1}=0$ and $A^k\ne0$.
The logarithm is its integer floor on positive $k$; all bounds, including
$n-1$ at zero dimension, are integer bounds. Neither $k=0$ nor a zeroth
power convention can settle this assertion. Both directions and both
arithmetic alternatives belong to this one target.

## Motivation

The source links binary expansions to degree doubling in natural squares.
It explicitly identifies control of cancellations as the obstacle to its
necessity argument. An exact ordinary-power certificate can test that
restriction without assuming that lower-power subspaces admit natural
bases inherited from the algebra.

## Gap

The maximal index bound and its attaining family are credited by the survey
to its references [30,35]; they do not classify all possible indices.
The survey reports finite computations in dimensions at most six and leaves
Conjecture 9 open. Its version history lists v1. The bounded arXiv
search for evolution algebras with nilpotency or spectrum returned 36
entries; titles of all entries and abstracts of the newest five supplied
no prior equivalent whole-question answer. Repository source and all-state
issue/PR checks likewise identified no prior equivalent resolution.
These checks reuse the source and duplicate assessments attached to
[research unit #21902](https://github.com/the-omega-institute/trureturing/issues/21902);
they are not an exhaustive literature or priority census.

## Route

Take $A=\mathbb Q^{15}$ with its standard coordinate basis
$e_1,\ldots,e_{15}$. Set all mixed products to zero and specify the natural
squares, in order, by

$$
\begin{aligned}
 e_1^2&=e_2+e_3+e_5,& e_2^2&=-e_4-e_5,& e_3^2&=e_4+e_5,\\
 e_4^2&=-e_6-e_8,& e_5^2&=e_6+e_8,& e_6^2&=e_7+e_8,\\
 e_7^2&=-e_9-e_{14},& e_8^2&=e_9+e_{14},& e_9^2&=e_{10},\\
 e_{10}^2&=e_{11},& e_{11}^2&=e_{12},& e_{12}^2&=e_{13}+e_{14},\\
 e_{13}^2&=-e_{15},& e_{14}^2&=e_{15},& e_{15}^2&=0.
\end{aligned}
$$

Extend this table bilinearly. The proof uses the following ordered spanning
vectors $v_1,\ldots,v_{15}$, which are not claimed to be a natural basis:

$$
\begin{gathered}
 e_1;\ e_2+e_3+e_5;\ e_3;\ e_4+e_5;\ e_5;\ e_6+e_8;\\
 e_7+e_8+e_9+e_{14};\ e_8;\ e_9+e_{14};\ e_{10}+e_{15};\\
 e_{11};\ e_{12};\ e_{13}+e_{14};\ e_{14};\ e_{15}.
\end{gathered}
$$

Their respective weights are

$$
(w_1,\ldots,w_{15})=(1,2,1,3,1,5,10,1,15,30,60,120,240,1,255).
$$

For each positive $m$, let $F_m$ span the $v_i$ with $w_i\geq m$.
The exact product table shows that a product $v_i v_j$ is zero or a vector
$v_\ell$ with $w_i+w_j\leq w_\ell$. Two span inductions give
$F_rF_s\subseteq F_{r+s}$ for arbitrary elements. Strong induction over
all positive splits gives $A^m\subseteq F_m$. The maximum weight is 255,
so $F_{256}=0$ and $A^{256}=0$.

The lower bound uses the degree pairs

$$
(1,1),(2,1),(3,2),(5,5),(10,5),(15,15),(30,30),(60,60),(120,120),(240,15).
$$

Starting with $v_1=e_1$ and the separate degree-one leaf $v_3=e_3$, the
successive outputs are $v_2,v_4,v_6,v_7,v_9,v_{10},v_{11},v_{12},v_{13},v_{15}$.
The final monomial has 255 leaves and equals $e_{15}\ne0$; hence
$A^{255}\ne0$. The ordinary nilpotency index is exactly 256.

At $n=15,k=255$, $k$ is not a power of two,
$\lfloor\log_2 255\rfloor=7$ and $s_2(255)=8$. Therefore
$7+8=15>14=n-1$. Existence holds while both proposed arithmetic
alternatives fail. This permitted rational example refutes the universal
iff in its entirety by disproving its necessity direction.

## Falsifier

The certificate would fail if the actual bilinear table lacked a natural
basis, if the fifteen vectors failed to span, if any product violated its
weight bound, if an ordinary positive split were omitted, or if the
255-leaf monomial vanished. The Lean proof discharges these conditions on
the explicit algebra. Substituting right powers, plenary powers, sampled
vectors or an unproved table assumption would not establish this result.

## Evidence

The endpoint is
`D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.result`,
with literal type `Not claim`. The public definition `claim : Prop` retains
the full universal equivalence. `indexExists` binds the actual vector
space, its module and finite-dimensional structures, bilinear product,
finrank, natural basis and consecutive-power conditions. `predicted`
contains both arithmetic alternatives with integer bounds.
`productSpace` and `ordinaryPower` encode the complete subspace recurrence;
`product` is the actual multiplication on the rational coordinate space.

The private `rational_instance` supplies a closed witness. The live proof
uses `power_le_filtration`, `filtration_mul`, the exact product and weight
tables, and `witness_255`; there is no unproved mathematical premise.
Finite coordinate normalizations are consumed helpers, not independent
results. The accepted axiom closure is contained in `propext`,
`Classical.choice` and `Quot.sound`.

The question, terminology and recurrence are attributed to the survey.
The concrete algebra, filtration and refutation are project results.
The [whole-question preregistration and unchanged forecasts](https://github.com/the-omega-institute/trureturing/issues/21902#issuecomment-6402959006)
identify the external target; this dossier adds no second question.

## Triage

- Proved: the rational fifteen-dimensional algebra has $A^{256}=0$ and
  $A^{255}\ne0$, so the original universal equivalence is false. A permitted
  witness suffices to refute it; an all-field construction is unnecessary.
- Proved mechanism: opposing natural-square components cancel in products
  of the displayed spanning vectors. The checked table nevertheless admits
  an additive weight filtration and a nonzero monomial with 255 leaves.
  Thus the proposed binary dimension restriction is not necessary in the
  original category. The filtration bounds every ordinary split, not only
  the ten splits used to construct the lower witness.
- Computed exactly within the proof: all ordered spanning-vector products,
  finite weight implications, reconstruction coordinates and the binary
  arithmetic at 255. No approximate experiment is a premise.
- Surviving boundary: this result does not disprove the proposed sufficiency
  direction, prove it, or classify the spectrum. Known maximal-index results
  quoted by the survey are not contradicted by this example. Their proofs
  and the source's low-dimensional observations are not re-established here.
- Unresolved: extensions of this certificate to every infinite field,
  characteristic restrictions, further dimensions and possible conditions
  restoring a necessity bound. No positive-sufficiency candidate is used.
- Effect: an argument requiring the proposed necessity cannot take
  Conjecture 9 as its premise. This refutation supplies no replacement
  spectrum theorem and settles no other question in the survey.
- Successor suggestions only: determine whether a separately specified
  restriction on natural-square cancellations restores a binary bound, or
  whether the rational certificate extends to other fields. Neither is an
  admitted external question or a separately counted resolution here.

## ASSUMED-UNVERIFIED

The checked source, arXiv metadata and repository ownership scope identified
no prior equivalent whole answer. Full citation closure, non-arXiv literature,
private or unposted results and worldwide priority remain unverified.
A verified prior equivalent would exclude new-resolution credit.
The mathematical conclusion rests on the closed Lean refutation, not on
these bounded absence checks. Independent publication reviews, required
CI and merge/dev inclusion are separate delivery obligations.
