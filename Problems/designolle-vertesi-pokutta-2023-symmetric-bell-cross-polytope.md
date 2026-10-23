---
slug: designolle-vertesi-pokutta-2023-symmetric-bell-cross-polytope
bibkey: designolle2023symmetricbell
doi: 10.1103/PhysRevA.109.022205
url: https://arxiv.org/abs/2310.20677v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.result
---

# Refutation of the symmetric Bell cross-polytope conjecture

## Problem

S. Designolle, T. Vértesi and S. Pokutta, *Symmetric multipartite Bell
inequalities via Frank-Wolfe algorithms*, arXiv:2310.20677v3 and
*Physical Review A* 109, 022205 (2024), DOI
10.1103/PhysRevA.109.022205, conjecture in Section V that the symmetrised
local polytope is affinely equivalent to the cross-polytope in dimension
$\lceil m/2\rceil$ for the stated multipartite range. The source defines
deterministic strategies and their local polytope in Eqs. (1)--(2), and the
symmetry generators in Eq. (25). The literal claim is encoded by
`D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.claim`.

## Motivation

The conjecture predicts that the projected deterministic strategy polytope
has exactly the cross-polytope extreme-point structure in every allowed
dimension. The settlement tests
three parties and seventeen inputs, where the proposed cross-polytope would
have dimension nine and eighteen extreme points.

## Gap

Preregistration [#15186](https://github.com/the-omega-institute/trureturing/issues/15186)
records the source statement, Lean conventions, route, and settlement
criteria before the formalization. The literature note records the source
version and the bounded search for a prior settlement. The conjecture remains
the source's stated open question within that scope.

## Route

The Lean model uses the real tensor carrier indexed by input tuples, the
signed permutation generators, the common fixed subspace, and the orthogonal
projection `Gamma`. The Reynolds average is the source's Eqs. (26)--(27).

For $N=3$ and $m=17$, the nine single-frequency strategies and their
negatives are uniquely exposed vertices. A mixed deterministic strategy has
scaled projected coordinates
$$
q_r = 289\,(\Gamma\,3\,17\,d)_{[r,0,0]}
  = (-141,133,-109,69,-13,-43,91,-123,139).
$$
The functional
$(-15,27,-21,8,59,24,-5,-6,10)$ takes value $8421$ on this point and at
most $8417$ on the eighteen frequency vertices. Thus the mixed point is
outside their convex hull, yielding at least nineteen extreme points.

## Falsifier

A proof of the encoded universal `claim` would falsify this settlement. At
the certificate level, the refutation would fail if the mixed point were not
in the projected local polytope, if the separating inequality did not hold,
or if the eighteen frequency points were not exposed as stated. The Lean
theorem `result : ¬ claim` discharges the certified instance at
$(N,m)=(3,17)$.

## Evidence

The settling source is
`D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.lean`.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). The supporting source is
`D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.lean`; its public
equality characterization has an unfinished escape audit under
[issue #15265](https://github.com/the-omega-institute/trureturing/issues/15265).
No registration file is delivered.

The experiment entry is [the pinned numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/7ee14723c2f0ce18f299a0f9870eb3d5330ee9e9/docs/reports/designolle-vertesi-pokutta-2023-symmetric-polytope-cross-polytope).
Command: `python3 check.py`, exit 0; script SHA-256:
`9cda6109955a66f89d7510741043b065bc600caf20e96a717b7f0dbd87dab998`.
The final reading is `bad= 0`. Its tested scope is:

- Reynolds coordinates: all 4096 strategies for $m=4$ and all 32768 for $m=5$, and 3000 random strategies each for $m=6,7$, at $N=3$.
- Table II: distinct symmetrised points at $N=3$, $m=3,\ldots,9$ are $10,10,60,100,640,1540,10032$.
- Smaller cases: at $N=3$ and $m=5,7,9,11,13$, the maximum computed $\ell_1$ norm of $V^{-1}q$ prints as $1.000000000000$; the floating-point containment check uses tolerance $10^{-9}$.
- Certificate: at $N=3$, $m=17$, the computed determinant is $98400527135576109875200$, the scaled point is $(-141,133,-109,69,-13,-43,91,-123,139)$, and the separator gives $8421>8417$. All $2^{17}$ sign vectors are checked at each odd frequency from $1$ to $17$; the maxima occur at 34 signed rotations for frequencies below 17 and at two for frequency 17.

## Triage

Tier 1 published conjecture; the Scribe attaches one
`OpenProblemResolutionClaim` with resolution `Refuted` for this dossier.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.result` | content | `nineteen_extreme`, using the invariant-basis construction and exact integer certificates | open-problem-resolution (#15186; Refuted) |

All private helpers in the settling module are consumed on the proof path of
`result`. The supporting theorem `sharp_norm_eq_iff` is content. The support module has eleven public theorem/lemma audit targets; their escape audit is unfinished under
[#15265](https://github.com/the-omega-institute/trureturing/issues/15265).
Every helper has a live consumer in the refutation dependency graph. The support module contains general all-$n$ results and has utility `none`; the settling module contains the finite certificates under its `certified-instance` / `refutes` utility. The published owner lemma `PeritoUnitCircleSum.abs_cos_sum_le` is also listed in the unfinished audit issue.

### What the settlement shows

**Proved by `result`:** the source's universal affine-equivalence conjecture
is false; the projected local polytope at $N=3$, $m=17$ has an extreme point
outside the eighteen frequency vertices, so it cannot be affinely equivalent
to a nine-dimensional cross-polytope.

**Proved mechanism:** `SymmetricBellPolytopeNotCrossPolytope.odd_frequency_norm_le` and
`norm_maximizers_are_rotations` give the sharp sign-sum bound and its signed
rotation maximizers. `freqVertex_exposed`, `altVertex_exposed` and
`signedVertex_extreme` in the settling module prove exposure of the eighteen
frequency vertices. `dot_wp`, `dot_wV_le` and `extraPoint_outside` prove the
integer separation $8421>8417$; `nineteen_extreme` supplies nineteen distinct
extreme points.

**Geometric explanation, proved by the following paper argument:** let
$\zeta=\exp(i\pi/17)$ and let $Z$ be the convex hull of the sums
$\sum_{r=0}^{16}\varepsilon_r\zeta^r$, with $\varepsilon_r\in\{\pm1\}$.
For a real linear functional with direction $u$, avoiding the seventeen
orthogonality directions, its unique maximizing sign vector selects the sign
of $\operatorname{Re}(\overline u\zeta^r)$. The phases occupy an interval
of length $16\pi/17<\pi$. Consecutive zeros of the cosine are $\pi$ apart,
so this sign vector has at most one change: it is a threshold with cut $k$
and initial sign $s$. Its sum is
$$
\sum_{r=0}^{16}\varepsilon_r\zeta^r
  = s\,\frac{2\zeta^k}{\zeta-1},
\qquad 0\le k\le17,\quad s\in\{\pm1\}.
$$
Every such threshold is selected by an open interval of directions (including
the two constant-sign thresholds). Since $\zeta^{17}=-1$ and $\zeta$ has
order $34$, the endpoint repetitions leave exactly $34$ distinct sums,
equally spaced on a circle. Every vertex of a finite planar convex hull can
be uniquely exposed by a direction avoiding that finite set of orthogonality
directions. Thus these sums are exactly the vertices of $Z$, which is the
regular $34$-gon. This is an explanatory geometric proof; no separate
kernel-checked polygon-equality theorem is delivered.

**Computed:** for odd $m=5,\ldots,13$ at $N=3$ the symmetrised polytope is the
indicated cross-polytope. The source's Table II counts for $N=3$ and
$m=3,\ldots,9$ are $10,10,60,100,640,1540,10032$.

**Computed readings:** the pinned experiment in [Evidence](#evidence) reports `bad= 0` on the exact finite scopes listed there, with its command, exit code and SHA-256.

**Open:** the first failing value among $m=14,15,16$ is not computed here;
other party counts remain open; and the source's remark that symmetric facets
are facets of the full local polytope for odd $N$ and even $m$ is not settled.

**Effect on neighbouring results:** the refutation changes the universal
cross-polytope conjecture and its proposed extreme-point description. It
does not refute the source's other Bell inequalities, Table II observations,
or the separate facet remark.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish exhaustive global novelty or
priority. The correspondence from the source's prose conjecture to the
encoded predicate is the preregistered interpretation in #15186. No
registration-completion state is claimed for the supporting public theorem.
