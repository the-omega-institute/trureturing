---
slug: bluhm-2025-four-qubit-compatibility-degree
bibkey: bluhm2025inclusion
doi: 10.48550/arXiv.2512.17706
url: https://arxiv.org/abs/2512.17706v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.result
---

# The exact compatibility degree of four dichotomic qubit measurements

## Problem

Bluhm, Evert, Klep, Magron and Nechita, *Inclusion constants for free spectrahedra
with applications to quantum incompatibility*, arXiv:2512.17706v1,
Conjecture 6.10, printed page 44:

> We conjecture that $s_{\mathbb C}(2,4)=2/\sqrt{13}$.

Definitions 2.13, 2.15 and 2.16 specify one joint POVM with the original effects
as marginals, white noise $E_i(s)=sE_i+(1-s)I/2$, the maximum feasible
$s\in[0,1]$, and the minimum of these degrees over all four-tuples.
Issue [#14687](https://github.com/the-omega-institute/trureturing/issues/14687)
preregisters this literal statement and its literature boundary.

## Motivation

The declaration `D5/S3/Quantum/Measurement/FourQubitCompatibilityDegree.result`
proves the conjecture with the source-defined degree. The lower bound applies
to all four-tuples of dichotomic POVMs on $\mathbb C^2$, including biased effects.
The minimum is attained by the trine-plus-perpendicular tuple.

## Gap

The source and literature checks in #14687 are attributed to their producers:
the codex-cli search seat supplied the candidate and analytic inequality; the
Claude Code orchestrator checked the source and recorded the literature reading.
No exhaustive priority or literature-search claim follows from these checks.
The older Appendix A.1 feasibility problem in the same source is a different statement.

## Route

For four vectors in $\mathbb R^3$, write
$M(x)=\max_{\varepsilon\in\{\pm1\}^4}\|\sum_i\varepsilon_i x_i\|$.
`FourVectorSignSumBound.four_vector_inequality` proves
$\sum_i\|x_i\|\le(\sqrt{13}/2)M(x)$.
`FourQubitParentConstruction.all_povms_compatible` turns this bound into a
joint measurement at $s=2/\sqrt{13}$ through compact sign decomposition,
antipodal parent effects and stochastic post-processing of biased effects.

The vectors
$(3,0,0)$, $(-3/2,3\sqrt3/2,0)$, $(-3/2,-3\sqrt3/2,0)$ and $(0,0,4)$
have total length $13$ and $M(x)^2=52$.
In `FourQubitCompatibilityDegree`, their associated tuple has a twelve-outcome
endpoint parent and a matching dual witness. Trace positivity yields
$26s\le4\sqrt{13}$ for every compatible noisy version of that tuple.
Compactness gives degree attainment; downward closure identifies the feasible
interval. `minimum_attained` and `result` establish the exact global minimum.

## Falsifier

A four-vector violation of the sharp inequality or a four-tuple with degree
below $2/\sqrt{13}$ would contradict the delivered kernel-checked declarations.
A claim of uniqueness requires a separate argument; attaining the optimum does
not establish uniqueness.

## Evidence

The three mathematical modules use the frozen `IsPOVM` predicate, existing
Pauli matrices, and pinned Mathlib. The axiom closure of every public declaration
is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The universal parent is a direct qubit construction; [BJN22] is not on its
proof dependency path. No BJN22 Library note is needed.

Escape audit unfinished:
[#14767](https://github.com/the-omega-institute/trureturing/issues/14767)
names all fourteen public theorem/lemma targets, including `result`, and the
missing source reconstruction, law bridge, variation, sensitivity and observational
dependence evidence. No validated four-slot registration is claimed.

## Triage

### What the settlement shows

- **Mechanism — proved.** `four_vector_inequality` uses the triangle decomposition
  of the four-sign constraint polytope and singular Gram positivity. The private
  `algebra_bound` obtains the sharp coefficient from the sign constraints and
  a nonzero null relation; four vectors in three dimensions supply that relation.
  Zero columns are handled separately. The construction attains equality at the
  trine-plus-perpendicular configuration. **Uniqueness up to symmetry — open**;
  no uniqueness argument is supplied.
- **Proposition 6.12, $g=4$ — proved by the reproducible Lean check below.**
  The vector program has greatest value $\sqrt{13}/2$, and
  $1/s_{\mathbb C}(2,4)=\sqrt{13}/2$. Scaling the extremal vectors by
  $1/\sqrt{52}$ gives the feasible attaining point; the universal four-vector
  inequality gives the upper bound. This proves the $g=4$ reading without [BJN22].
- **Nine-year numerical lineage — proved exactness; literature attribution.**
  Conjecture 6.10 identifies the numerical value of Bavaresco et al. (2017),
  [BQG+17], and says its optimality would follow from the conjecture.
  `result` supplies the exact value $2/\sqrt{13}$. The historical attribution
  is a reading of that source, not an independent reconstruction of the 2017 numerics.
- **$g=5$ and higher — open.** The delivered triangle decomposition is specific
  to four vectors. It supplies no value of $s_{\mathbb C}(2,g)$ for $g\ge5$,
  and no higher-$g$ numerical reading is computed.
- **General-$d$ Section 6 conjectures — open.** Remark 6.11 and the $d=3$
  numerics are outside this theorem's scope. Their status is unaffected.

### Reproducible vector-program evidence

Experiment entry: [`docs/reports/bluhm-2025-four-qubit-compatibility-degree/check.lean`](https://github.com/the-omega-institute/trureturing-experiments/blob/602ec65402d492351ebc19230b04caa93001cda8/docs/reports/bluhm-2025-four-qubit-compatibility-degree/check.lean) in `the-omega-institute/trureturing-experiments` at `602ec65402d492351ebc19230b04caa93001cda8`. The program is run from a trureturing checkout with `lake env lean <path>/check.lean`. Exit code: 0. Source SHA-256: `e4bbc7efd743e7bb977aa36f5bb5cdd8f671b5158fd4e72bcc716484c09587af`.
The tested scope is exactly four vectors in $\mathbb R^3$ and four dichotomic qubit measurements. Its three `example` proofs are kernel checks of delivered declarations: the optimum value √13/2, `1 / minCompatDegree = √13/2`, and attainment of the minimum. They add no mathematical declaration to the delivery.

## ASSUMED-UNVERIFIED

The literature boundary is the searched scope recorded in #14687; it is not a
proof that no independent settlement exists outside that scope. Uniqueness,
higher-$g$ values and higher-dimensional conjectures remain open. The escape
audit has the missing evidence specified in #14767.
