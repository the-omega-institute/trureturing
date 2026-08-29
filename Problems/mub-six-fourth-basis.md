---
slug: mub-six-fourth-basis
bibkey: mcnultyweigert2024mutually
arxiv_id: 2410.23997
triage: wall
motivation_gids:
  - D5/S3/Quantum/Tomography/RankOneContextCommutator
  - D5/S3/Quantum/Tomography/CompleteContextTomography
  - D5/S3/Quantum/Tomography/ComplementaryContextProbabilityPythagoras
  - D5/S3/QuantumBounds/Designs/CollisionConservation
---

# A fourth mutually unbiased basis in dimension six

## Problem

Does there exist a family indexed by `Fin 4` of orthonormal bases of
six-dimensional complex space such that vectors from distinct bases have
squared inner-product magnitude exactly `1 / 6`? Dimension six is known to
admit three mutually unbiased bases, while a complete family would contain
seven. The MUB form of Zauner's conjecture asserts that at most three exist.

This dossier deliberately anchors Problem 10.2 of arXiv:2410.23997v2: "Show
that no set of four MU bases exists when d = 6." It retains Conjecture 2.1 as
Zauner's original formulation, whose affine quantum-design parameters have
`b = g = 6`, `r = 1`, `lambda = 1 / 6`, and `k = 4`. Problem 10.1 is the
comparison statement for `Fin 7`: "Show that no complete set of seven MU bases
exists when d = 6." Conjecture 1.1 likewise concerns complete MUB families in
composite dimensions that are not prime powers. Nonexistence at `Fin 4` implies
nonexistence at `Fin 7`, while nonexistence at `Fin 7` does not by itself
exclude `Fin 4`; the former is therefore the stronger nonexistence statement.

Here "Zauner's conjecture" means this MUB upper-bound conjecture. It is not the
same conjecture as the identically named SIC-POVM existence conjecture in all
dimensions.

The review also reports fourteen mathematically equivalent formulations of the
complete-set existence problem. In dimension six they concern `Fin 7`, not the
`Fin 4` fourth-basis problem. They are source-side routes, not fourteen
repository theorems.

## Motivation

- `D5/S3/Quantum/Tomography/RankOneContextCommutator.lean` supplies
  `RankOneContext`, `overlap`, `incompatibility`, and
  `aggregated_rank_one_context_commutator`. These declarations already express
  the rank-one projector geometry needed for a conditional MUB consequence.
- `D5/S3/Quantum/Tomography/CompleteContextTomography.lean` supplies
  `complete_context_tomography`. It accepts a family
  `Fin (n + 2) -> RankOneContext (n + 1)`, assumes the required overlap
  identities, and proves consequences of that family. It is not evidence that
  such a family exists.
- `D5/S3/Quantum/Tomography/ComplementaryContextProbabilityPythagoras.lean`
  separates visible centered-probability mass from an orthogonal residual.
- `D5/S3/QuantumBounds/Designs/CollisionConservation.lean` supplies
  `collision_sum_eq_one_add_purity`, deriving
  `sum = 1 + trace (rho * rho)` only under its finite projective two-design
  hypothesis `hdesign`. A union of MUBs supplies that design structure only at
  `mu >= d + 1`, which is at least seven bases for `d = 6`. This dossier has no
  bridge from a `Fin 4` family to `hdesign`, so the theorem is complete-set
  (`Fin 7`) background or a candidate requiring a new bridge, not a necessary
  constraint on the `Fin 4` feasible set.

These are nearby exact identities. None decides whether four MUBs exist in
dimension six.

## Gap

The orchestrator's full-tree fixed-string search measured zero D5 hits for
`MutuallyUnbiased`, `mutually_unbiased`, `MutuallyUnbiasedBases`,
`ComplexHadamard`, `complexHadamard`, and `HadamardMatrix`, with
`RankOneContext` as a positive control. The term `unbias` occurs only in two
existing modules' library-search comments. Case-insensitive `hadamard` occurs
in three modules, all concerning Hadamard gates or coordinate transforms rather
than complex Hadamard matrices.

Consequently the repository has no MUB-family definition, no equivalence
between orthonormal bases and rank-one contexts, and no internal formalization
of order-six complex Hadamard matrices. The external classification landscape
has changed: arXiv:2608.18053, published 2026-08-18, claims a complete and exact
finite-incidence classification of order-six complex Hadamard matrices. That
preprint was submitted to arXiv on 2026-08-18 at 17:46:58 UTC and was not
independently verified here; its peer-review status was not measured for this
dossier. Its classification is evidence, not a theorem used by this dossier.
The remaining gap is a joint compatibility or exclusion argument over the
claimed classified atlas, together with the basis-context bridge, that rules
out a `Fin 4` family. The existing tomography theorems assume complementary
families and derive consequences; they do not construct or exclude that family.

## Route

The first reachable statement uses only existing declarations and has this
shape:

```text
(context : Fin 4 → RankOneContext 6)
(h : ∀ l k, l ≠ k → ∀ j r,
  overlap (context l) (context k) j r = 1/6)
⊢ ∀ l k, l ≠ k →
  incompatibility (context l) (context k) = 1
```

This is a conditional bridge: it assumes that the four contexts exist and
derives their maximal pairwise incompatibility. It proves neither existence
nor nonexistence. No Lean file is added in this round.

Subsequent work would have to proceed in separate, measured steps:

1. Promote the compiled conditional-bridge probe into a committed Lean
   declaration and connect its conclusion to the aggregated rank-one
   commutator identity.
2. Establish an exact basis-to-`RankOneContext` equivalence before translating
   the source's MUB or complex-Hadamard formulations.
3. For complete-set (`Fin 7`) background only, formalize selected members of
   the review's fourteen equivalent formulations. Use collision conservation
   only under its `hdesign` hypothesis unless a new theorem bridges `Fin 4` to
   that hypothesis; no such bridge is supplied here.
4. Independently verify and, where needed, formalize the exact finite-incidence
   atlas claimed by arXiv:2608.18053, then establish a joint compatibility,
   inequality, or certificate over that atlas strong enough to exclude
   `Fin 4`. The classification claim or finite optimization output alone cannot
   close this step.

## Falsifier

A concrete exact family of four pairwise mutually unbiased bases in dimension
six would refute the nonexistence conjecture. Conversely, failure to find such
a family in a finite search is not a finite certificate of nonexistence; this
dossier supplies no finite certificate that rules out every family.

The conditional bridge is finitely falsifiable and must be kept separate from
the conjecture. Four explicit `RankOneContext 6` values satisfying the stated
overlap hypotheses but with a distinct pair whose `incompatibility` is not one
would refute that bridge.

## Evidence

arXiv:2203.09429, *Three numerical approaches to find mutually unbiased bases
using Bell inequalities*, by Prat Colomer, Mortimer, Frérot, Farkas, and Acín,
reports three numerical methods. Its abstract states:

> "In the smallest composite dimension, six, it is known that between three
> and seven mutually unbiased bases exist, with a decades-old conjecture,
> known as Zauner's conjecture, stating that there exist at most three."

> "All three methods correctly identify the known cases in low dimensions and
> all suggest that there do not exist four mutually unbiased bases in
> dimension six."

The authors explicitly decline to treat the heuristic optimum values as a
rigorous proof. These computations are evidence against existence, not a
nonexistence theorem.

arXiv:2606.13903, *Degree-Four Vector-Coordinate SoS Cannot Detect the MUB
Upper Bound*, excludes one route: degree-four vector-coordinate
sum-of-squares cannot detect the MUB upper bound. This negative result is
recorded so that the same relaxation is not presented again as a path to the
dimension-six proof. It does not exclude higher-degree or differently encoded
methods.

**ASSUMED-UNVERIFIED:** arXiv:2608.18053, *A Complete Classification of
Complex Hadamard Matrices of Order Six*, by Mateo Cárdenes Wuttig and Joseph
Tindall, was published 2026-08-18. Its abstract says that the order-six
classification had remained open for decades, claims a complete and exact
finite-incidence classification up to standard equivalence, reports a proof of
Szöllősi's conjecture, and names applications to balanced six-mode
interferometers and mutually unbiased bases. Its mathematical claims were not
independently checked for this dossier and are not used as established
theorems; its peer-review status was not measured.

## Triage

`wall`. The repository has exact consequences of complementary rank-one
contexts but lacks the MUB carrier, the basis-context bridge, and the
classification needed to decide `Fin 4` in dimension six.

The nearby Zauner-named formal material does not change that boundary.
`D5/S3/QuantumContext/ZaunerSymplecticMatrix.lean` is a certificate for the
explicit matrix `!![6,23;19,17]` over `ZMod 24` and its fixed vector;
`D5/S3/QuantumContext/CliffordPhaseKernel.lean` is 38 lines. Neither supplies a
dimension-six MUB classification.

The current consumption boundary has no live repository entry point.
`Problems/` is not part of a machine-selected repository candidate set. There
is no periodic scan, automatic ingestion, or machine-derived consumed/discarded
lifecycle. This dossier therefore records an external open problem; it does not claim
sustained automated consumption or that the repository can solve or advance
the conjecture.

## ASSUMED-UNVERIFIED

- Openness records the statement in version 2 of the review, not an exhaustive
  search of all literature published after that version.
- No Lean declaration is added in this round. During the original implementation,
  `find .lake/build -name '*.olean'` printed zero paths in both the primary
  checkout and the worktree (both commands exited 0), so the orchestrator did
  not rerun the probe then. During review, `find .lake/build -name '*.olean' |
  wc -l` returned 1412 (exit 0), including
  `.lake/build/lib/lean/D5/S3/Quantum/Tomography/RankOneContextCommutator.olean`.
  The orchestrator then ran `lake env lean <probe.lean>` on the Route's exact
  statement: `PROBE_EXIT=0`, wall time 20.997 seconds (2.30 seconds user and
  4.33 seconds system), with no output or warnings. Replacing `1 / 6` by
  `1 / 5` was confirmed by `grep -c '1 / 5'` returning 1; the mutated probe
  reduced to `False` and returned `MUT_EXIT=1`. This checks the scratch proof's
  compilability and a negative control, but the statement remains uncommitted
  probe text rather than a repository Lean declaration or a registered
  frontier result.
- The claims of arXiv:2608.18053 are unreviewed and have not been independently
  verified for this dossier.
- The review's fourteen equivalent formulations have not been checked one by
  one.
