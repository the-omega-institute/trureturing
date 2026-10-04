---
slug: barei-2026-remark-3-5-minimal-idempotent
bibkey: barei2026solvable
doi: null
url: https://ai.meta.com/research/publications/on-solvable-evolution-algebras-and-a-conjecture-by-garcia-martinez-and-perez-rodriguez/
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.result
---

# A three-dimensional minimal idempotent subspace

## Problem

Barei, with Muse Spark via meta.ai and review by Nicolás Jaramillo Torres,
states in Remark 3.5:

> Given a finite-dimensional evolution algebra E, we are yet to find idempotent subspaces of dimension greater than two which do not properly contain a nontrivial idempotent subspace.

The reading fixed in [#12879](https://github.com/the-omega-institute/trureturing/issues/12879)
is an existence question over ℂ. An evolution algebra is a vector space with a
bilinear, possibly nonassociative multiplication and a natural basis whose
mixed products vanish. For every complex linear subspace U, let
$U^2=\operatorname{Span}_{\mathbb C}\{xy:x,y\in U\}$. Idempotent means
$U^2=U$, and nontrivial means nonzero. V is not required to be an evolution
algebra in its own right. Minimality ranges over all complex linear subspaces,
not only coordinate subspaces or subspaces defined over ℚ.

The precise positive answer is: there exist such an E and V with
$\dim_{\mathbb C}V=3$, $V^2=V$, and
$U\le V$, $U\ne0$, $U^2=U$ implying $U=V$ for every U.
The displayed remark is an unresolved search, not an asserted universal
nonexistence theorem. Barei's Example 2.1 is literature and is excluded.

## Motivation

The result separates minimal idempotent subspaces from idempotent lines and
from subspaces possessing natural bases. A square-zero plane can coexist
with an idempotent three-dimensional subspace while forbidding smaller
nonzero idempotent subspaces. The single formal target is
`D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.result`.

## Gap

The named, numbered remark in a recent external publication is a tier-1
question. The five-dimensional realization answers its greater-than-two
search. The preregistration is #12879 under its issue-specific
[owner ruling](https://github.com/the-omega-institute/trureturing/issues/12879#issuecomment-5978205663).

**Provenance disclosure:** an exploratory session outside this repository
already produced and compiled `muse-evolution-local/Extension.lean` on
2026-10-04, and `REPORT.md` already contained the written proofs in B1/B2 and
literature readings in B6. Thus #12879 was **not filed before any Lean**.
The owner accepts this disclosed chronology gap for this issue only; no
other §3.2(a)–(d) condition is waived. The prior producer/model identity is
not established by those local files. This repository port is produced by
Codex (GPT-6) using `formal-thinking-and-answer`; its exact statement adds
bilinearity, an actual basis and the finrank conclusion to the prior
ambient minimality certificate.

Fresh bounded readings on 2026-10-04:

- Barei's publication page and linked PDF returned HTTP 200. PDF SHA-256:
  `0133eb2e4d3a2cf868ab47856598a16906e2ddf0980f1a413d91e04ee536261f`.
  The text extraction equals the supplied source. §§2–3 were read.
- Hu–Wen, arXiv:2609.25023v1, Theorem 2.1, the stable plane and zero-algebra
  direct sums, and Proposition 2.8: the stable dimension is two and padding
  preserves it. These are prior counterexamples, not this target.
- Costoya–Fernández Ouaridi–Viruel, arXiv:2609.32784v1, Theorems 2.1/3.5,
  Proposition 3.8, Remark 3.9 and §4: the general evolution-envelope and
  quadratic-map embedding framework is prior literature. Its explicit
  intrinsic counterexample is two-dimensional. Minimal ambient embedding
  dimension differs from minimality among idempotent subspaces. The
  construction below is in that framework's spirit.
- García-Martínez–Pérez-Rodríguez, arXiv:2512.12418v1, Theorem 3.5 and
  Conjecture 3.6: these concern regular evolution algebras and solvability,
  rather than an answer to this higher-dimensional subspace question.
- Fresh arXiv metadata query `ti:"evolution algebras"` returned all 92 of
  92 entries; titles and abstracts were screened. Query
  `all:"idempotent subspace"` returned zero entries. This is metadata
  screening, not full-text inspection of every listed work.
- Repository semantic-surface text screening found no evolution-algebra
  or idempotent-subspace result. Pinned Mathlib text screening found no
  exact target. GitHub code searches for `"evolution algebra" language:Lean`
  and `"idempotent subspace" language:Lean` each returned zero results.
  Standard basis, span and finrank APIs are reused directly.

No answer was found in this searched scope. This is bounded diligence,
not an exhaustive absence or priority claim.

## Route

Let E have natural basis $e_1,\ldots,e_5$, all mixed products zero. Put
$u=e_1+e_2+e_3+e_4+e_5$, $v=e_2-e_3$, $w=e_4-e_5$, and set

$$
e_1^2=4u+2w,\quad e_2^2=v,\quad e_3^2=-v,\quad
 e_4^2=v+w,\quad e_5^2=-v-w.
$$

The injective linear map
$\phi(a,b,c)=(a,a+b,a-b,a+c,a-c)$ has range $V=\operatorname{Span}\{u,v,w\}$.
The first coordinate recovers a, and the second and fourth recover b and c,
so $\dim V=3$. Direct multiplication yields

$$
u^2=4u+2w,\quad uv=2v,\quad uw=2v+2w,\quad v^2=vw=w^2=0.
$$

These products span V: uv supplies v, uw then supplies w, and u² supplies u.
Thus $V^2=V$. Bilinearity follows coordinatewise from the diagonal ambient
product; the standard coordinate basis is an actual natural basis.

If U is a subalgebra of V and contains $x=au+bv+cw$ with $a\ne0$, set

$$
s=x^2-4ax=4acv+2a^2w,\qquad xs-2as=4a^3v.
$$

Both expressions belong to U. Division by their nonzero scalar coefficients
puts v in U, then w, then u. Hence U=V. Otherwise U lies in the square-zero
plane $W=\operatorname{Span}\{v,w\}$, so $U^2=0$. Since an idempotent
subspace is a subalgebra, a nonzero idempotent U≤V must equal V.

## Falsifier

A nonzero proper complex linear subspace U≤V with its full pair-product span
equal to U would contradict the conclusion. Failure of bilinearity, linear
independence of the three embedded vectors, or the natural-basis condition
would invalidate this witness. Checking only coordinate subspaces would
not answer the stated question.

## Evidence

Canonical source:
`D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.lean`.
The public surface is `E`, `Square` and one theorem `result`. Private
definitions encode intrinsic coordinates and the ambient witness; all
proof steps are local facts inside `result`, not companion theorems.

`result` existentially supplies a complex bilinear map, an actual
`Module.Basis (Fin 5) ℂ E`, and V, and states ambient finrank five, vanishing
mixed basis products, finrank three, square equality and universal
subspace minimality. The formal claim is exactly this existential statement;
the general-dimensional arguments in Triage are separate written mathematics.

## Triage

Tier 1; intended resolution `Proved`; `admission_basis: open-problem-resolution`
under #12879 and its owner ruling. Per-declaration assessment:
`E` and `Square` are definitions; `result` has `proof_shape: content`.
Its live algebraic generation argument establishes a classification of
all subalgebras of V beyond basis/span/dimension library normalization.
Direct project-frozen prerequisites: none, pinned Mathlib only.

Utility `kind=none`: the proof quantifies over arbitrary complex vectors and
all complex subspaces. It is structural algebra, not bounded enumeration,
a reflection checker, a numerical-estimate reduction or a finite computation
certifying one searched instance. Coordinate arithmetic does not supply
minimality by itself. Other utility fields are not applicable to kind none.
This semantic classification remains subject to independent review.

**Proved by written argument, not formalized (B2): arbitrary d≥2.**
Let m=d−1, over any field of characteristic different from two. Give E_d the
natural basis $f_0,f_i^+,f_i^-$ for $1\le i\le m$. Set
$u=f_0+\sum_i(f_i^++f_i^-)$, $w_i=f_i^+-f_i^-$, and $w_0=0$, with

$$
f_0^2=4u+2w_m,\qquad (f_i^+)^2=w_i+w_{i-1},\qquad
(f_i^-)^2=-w_i-w_{i-1}.
$$

Then V_d=Span{u,w₁,…,w_m} has dimension d; W=Span{w₁,…,w_m} has zero
multiplication. Let $Nw_i=w_{i-1}$ and $T=L_u|_W=2(I+N)$. Since N is
nilpotent, T is invertible, so $uW=W$ and u² supplies u: $V_d^2=V_d$.
If a subalgebra contains u+z, set S=U∩W. For s∈S, $(u+z)s=Ts\in S$;
therefore S is N-invariant. Moreover

$$
(u+z)^2-4(u+z)=2w_m+4Nz\in S.
$$

This vector and its successive N-images form a triangular basis of W with
leading coefficients 2. Thus S=W and U=V_d. All other subalgebras lie in W
and have zero multiplication, proving minimality. The natural-basis squares
also span V_d, hence $E_d^2=V_d$.

**Proved by written argument, not formalized (B2): embedding bound for this
intrinsic family.** In any evolution embedding of A_d=V_d into dimension n,
with column-square matrix M, perfectness gives rank M≥d. The coordinate
image J of its square-zero plane has dimension m and
$M(z\odot z)=0$ for all z∈J. Choose m independent coordinate projections
on J and vectors whose projected coordinates are the standard basis. Their
coordinatewise squares remain independent, so
$\dim\ker M\ge\dim\operatorname{Span}\{z\odot z:z\in J\}\ge m$.
Rank-nullity gives n≥d+m=2d−1. The displayed realization attains this bound.
This bound is for A_d, not all possible intrinsic algebras of dimension d.

**Computed in prior local work, not repository-certified:** REPORT.md B2
reports exact symbolic checks for d=2,3,4,5. Those files were not rerun in
this delivery; the written general proof above supplies the mathematical
argument without those computations.

**Open (B7):** whether a different three-dimensional minimal idempotent
subspace can occur in a four-dimensional complex evolution algebra;
classification up to intrinsic algebra isomorphism of all minimal idempotent
subspaces of dimension at least three; broader prior-literature status of
the exact Jordan family. The family-specific embedding lower bound does
not exclude the first question. Characteristic-two constructions mentioned
in the prior report are outside this formal delivery, with their broader
literature status also open.

## ASSUMED-UNVERIFIED

The bounded literature readings do not establish global priority. The
older full classifications and the complete citation graph were not
independently traversed. The general-dimensional proof and its embedding
bound above are written mathematics, not additional Lean-verified
statements. Prior symbolic computations are identified as prior reports.
Kernel verification does not authenticate the external publication or
its version history. Information-escape registration is paused by
CLAUDE.md §3.9; this delivery does not claim `declared_validated`.
