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
symmetry generators in Eq. (23). The literal claim is encoded by
\`D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.claim\`.

## Motivation

The conjecture predicts that the projected deterministic strategy polytope
has exactly the cross-polytope extreme-point structure in every allowed
dimension. The settlement tests the first case beyond the computed examples:
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
projection \`Gamma\`. The Reynolds average is the source's Eq. (27), and the
fixed-coordinate description is Eq. (28).

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

A proof of the encoded universal \`claim\` would falsify this settlement. At
the certificate level, the refutation would fail if the mixed point were not
in the projected local polytope, if the separating inequality did not hold,
or if the eighteen frequency points were not exposed as stated. The Lean
theorem \`result : ¬ claim\` discharges the certified instance at
$(N,m)=(3,17)$.

## Evidence

The settling source is
\`D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.lean\`.
Its designated public result is the refutation result
(\`basis=refutes\`), which is exempt from four-slot escape registration under
CLAUDE.md §3.9. The supporting source is
\`D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport.lean\`; its public
equality characterization has an unfinished escape audit under
[issue #15265](https://github.com/the-omega-institute/trureturing/issues/15265).
No registration file is delivered.

The experiment entry
\`docs/reports/designolle-vertesi-pokutta-2023-symmetric-polytope-cross-polytope/check.py\`
in \`the-omega-institute/trureturing-experiments\` is pinned to commit
\`7ee14723c2f0ce18f299a0f9870eb3d5330ee9e9\`. The recorded command is
\`python3 check.py\`, exit code 0, script SHA-256
\`9cda6109955a66f89d7510741043b065bc600caf20e96a717b7f0dbd87dab998\`,
with final reading \`bad= 0\`. It checks the Reynolds coordinates, the
source's Table II values, the smaller odd cases, and the $m=17$ certificate.

## Triage

Tier 1 published conjecture; the Scribe attaches one
\`OpenProblemResolutionClaim\` with resolution \`Refuted\` for this dossier.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| \`D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.result\` | content | none | open-problem-resolution (#15186; Refuted) |

All private helpers in the settling module are consumed on the proof path of
\`result\`. The supporting theorem \`norm_maximizers_are_rotations\` is content
and its unfinished audit is linked above; its other public helpers are
bind-only and consumed by the support proof and the settling result.

### What the settlement shows

**Proved by \`result\`:** the source's universal affine-equivalence conjecture
is false; the projected local polytope at $N=3$, $m=17$ has an extreme point
outside the eighteen frequency vertices, so it cannot be affinely equivalent
to a nine-dimensional cross-polytope.

**Mechanism proved in the formal route:** the single-frequency sign sums form
the sharp regular half-circle bound and remain uniquely exposed after the
three-party projection. The mixed strategy is separated by the integer
functional with $8421>8417$, producing the additional extreme direction.

**Computed:** for odd $m=5,\ldots,13$ at $N=3$ the symmetrised polytope is the
indicated cross-polytope. The source's Table II counts for $N=3$ and
$m=3,\ldots,9$ are $10,10,60,100,640,1540,10032$.

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

