---
slug: mathoverflow-512655-cyclic-sign-trace-affine-support
bibkey: ricardorr2026mo512655
doi: null
url: https://mathoverflow.net/questions/512655
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/RankAssembly.affine_trace_support_dimension
---

# Affine support of the odd cyclic sign-matrix trace

## Problem

Ricardorr (MathOverflow user 49534; real-name attribution unverified) asks in
[question 512655](https://mathoverflow.net/questions/512655), revision 1,
GUID `E06A6743-2C15-41CD-9390-04D1862ABA02`:

> For every odd $n$ and every nonzero $b$, does the affine hull of
> $\mathrm{Supp}(b)$ have dimension at least $n-1$? Equivalently: is
> $\mathrm{Supp}(b)$ contained in no affine subspace of codimension $\ge 2$?

The [original revision](https://api.stackexchange.com/2.3/revisions/E06A6743-2C15-41CD-9390-04D1862ABA02?site=mathoverflow&filter=withbody)
is attributed under CC BY-SA 4.0. The title's hyperplane wording is a locator;
the target is the dimension lower bound in the body.

Precisely, let $n$ be any positive odd integer, $b\in\mathbb F_2^n$ nonzero,
and $a\in\mathbb F_2^n$. All indices are modulo $n$. Put
$g_k=a_{k-1}$ and $h_k=a_k+a_{k-2}+b_k$ in $\mathbb F_2$, and define the
integer matrix

$$
A_k(a)=\begin{pmatrix}1&1\\(-1)^{h_k}&(-1)^{h_k+g_k}\end{pmatrix}.
$$

Equivalently, its entry indexed by $s,t\in\{0,1\}$ is
$(-1)^{h_ks+g_kst}$. With the literal ordered integer product, set

$$
W_b(a)=\operatorname{Tr}(A_0(a)A_1(a)\cdots A_{n-1}(a)),\qquad
\mathrm{Supp}(b)=\{a\in\mathbb F_2^n:W_b(a)\ne0\}.
$$

The assertion is
$\dim_{\mathbb F_2}\operatorname{aff}(\mathrm{Supp}(b))\ge n-1$.
Length one, coincident cyclic indices, every nonzero mask, and every tested
word including zero and all-one are included. There is no length or weight
cutoff, additional nonempty-support premise, or equality assertion.

## Motivation

The question connects an ordered matrix trace to the affine geometry of a
Boolean Fourier support. The source reports a weaker bound $(n-1)/2$, checks
through odd lengths at most 21, and a five-bit hyperplane example. Those source
observations do not settle the universal inequality.
`D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/RankAssembly.affine_trace_support_dimension`
proves the complete lower bound for $n=2m+1$, every natural $m$, and every
nonzero $b$.

## Gap

The source's inverse-chi discussion needs both a trace-to-Walsh identity in
the correct orientation and a dimension bound for every nonzero component,
rather than a single active input bit. The retained proof supplies these
bridges and the arbitrary-mask bound. It assumes no derivative-space
classification, coefficient uniqueness, or affine-dimension conclusion.
Preregistration issue [#25520](https://github.com/the-omega-institute/trureturing/issues/25520)
fixes this full source event.

## Route

The owning Scribes give the definitions and full derivation. In outline:

1. Expand the ordered trace as a sum over cyclic binary paths and identify
   its exponent with the phase of
   $\chi_i(x)=x_i+x_{i+2}+x_{i+1}x_{i+2}$.
2. Prove the odd-cycle inverse and change variables. The trace support is
   exactly the Walsh support of $y\mapsto b\cdot\chi^{-1}(y)$.
3. Relate its affine direction to the subspace of constant derivatives by
   annihilator duality. Their dimensions sum to $n$.
4. Extract actual Boolean function coefficients of the shifted inverse.
   Top-degree, endpoint and lower-degree equations constrain derivative
   directions. For a nonzero mask at length at least five, the mask is
   all-one or has an active bit with an inactive predecessor by two. At
   such a boundary all direction coordinates are determined by one
   coordinate; the all-one case forces the direction to vanish. Coordinate
   evaluation is therefore injective into $\mathbb F_2$.
5. At length three the endpoint equations give the same dimension bound;
   at length one the required lower bound is zero. Duality then gives
   affine dimension at least $n-1$, including length five directly.

## Falsifier

A counterexample to the external assertion would be a positive odd $n$,
nonzero $b$, and the specified integer trace support with affine dimension
less than $n-1$. A trace/index/sign mismatch or a failure of the exact Walsh
orientation would invalidate application of a Fourier result to this source.
The formal theorem uses the literal ordered trace and proves those identities;
finite checks or a bound for a restricted mask family would not suffice.

## Evidence

The declaration's actual source owner is
`D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/RankAssembly.lean`.
Its statement is

$$
\forall m\in\mathbb N\;\forall b\in\operatorname{Word}(2m+1),\quad
b\ne0\;\Longrightarrow\;
2m\le\operatorname{finrank}_{\mathbb F_2}
\bigl(\operatorname{affineSpan}_{\mathbb F_2}(\operatorname{traceSupport}(b))\bigr)
 .\operatorname{direction}.
$$

The statement identity is
`sha256:2826b759226e068c83e31ad138e36d16e64de5c4a887d35d2f47a51ac6d6b4c8`;
its type identity is
`sha256:ef637381ab103d940937e2bed6eef2eeefdda16079e3c0d9f4172cdd9fa12ee4`.
The kernel-checked theorem uses only `Classical.choice`, `Quot.sound`, and
`propext`. The Lean source is the mathematical authority; the typed Scribe
claim binds this dossier to that frozen theorem.

The proof reuses pinned Mathlib finite-dimensional linear algebra, character
sum interfaces, finite sums and matrices, plus the repository's `bit_cases`.
The cyclic inverse derivation, literal ordered-trace bridge, Boolean
coefficient constraints and arbitrary-mask rank assembly are repository
contributions, rather than a claim that the surrounding Fourier machinery is
new. The auxiliary escape registrations remain unfinished as disclosed in
[#25520](https://github.com/the-omega-institute/trureturing/issues/25520#issuecomment-6580142201);
this resolution binding does not certify those registrations.

## Triage

Tier 1 specialized external author-posed question; `theorem`.
The endpoint has `proof_shape: content` and
`admission_basis: open-problem-resolution`. Its single resolution member is
the actual RankAssembly theorem above. The support owners retain their own
content witnesses and consumed helpers; the import facade is not a separate
mathematical result. The theorem proves a lower bound, without classifying all
masks attaining equality or asserting that every support is a hyperplane.

## ASSUMED-UNVERIFIED

The bounded source search inspected Daemen's thesis §§6.6.2 and 6.9, the
Keccak reference 3.0 §2.3.1, the relevant Guo–Liu–Song ASIACRYPT 2016
sections, and Mella–Mehrdad–Daemen, *Differential and Linear properties of
vectorial boolean functions based on chi*, Cryptography and Communications
15 (2023), 1087–1116, [DOI 10.1007/s12095-023-00639-1](https://doi.org/10.1007/s12095-023-00639-1),
§6.4. The latter's single-active-input-bit propositions do not state this
arbitrary-nonzero-mask assertion. Omland–Stanica ePrint 2022/279 was unread
after an access failure. Broader literature was not exhausted. No worldwide
openness, originality, priority, or absence of independent proofs follows
from this search. The source's finite checks and example are reported source
claims, not additional independently verified results of this dossier.
