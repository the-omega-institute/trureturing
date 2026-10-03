---
slug: bernards-guhne-2022-hybrid-nonlocality-depth-bound
bibkey: bernards2023nonlocalitydepth
doi: 10.1103/PhysRevA.107.022412
url: https://arxiv.org/abs/2205.04250v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/HybridMerminDepthBound.result
---

# Bernards–Gühne hybrid classical bound

## Problem

F. Bernards and O. Gühne, *Bell inequalities for nonlocality depth*,
arXiv:2205.04250v2, Phys. Rev. A 107, 022412 (2023), Section III.F,
Eq. (28), define

$$F_n=\sum_{\ell=1}^n(-1)^{1+\lceil\ell/2\rceil}\ell
(1\ldots1\,2\ldots2)\le n2^{n-2}.$$

The bracket contains $n-\ell$ settings 1 and $\ell$ settings 2,
and sums distinct party permutations. Section V states:

> For (k, m) models with m > 2, we have a conjecture for the classical
> bound. Proving this bound or finding a counterexample remains an open problem.

Issue #12316 preregisters this Tier 1 question, its source, full quantifiers,
interpretation and literature check. The encoded claim is the sharp bound
for every $k,m\ge2$ with $n=k+m$, including $m>2$.

## Motivation

`D5/S3/QuantumBounds/HybridMerminDepthBound.result` proves `claim`:

$$\forall k,m\in\mathbb N,\quad k\ge2\Longrightarrow m\ge2
\Longrightarrow\max_{A,B}F_n(A,B)=n2^{n-2}.$$

Here $A:\{0,1\}^k\to\{\pm1\}$ and
$B:\{0,1\}^m\to\{\pm1\}$ are arbitrary deterministic cell responses.
Section II explicitly allows signaling inside a cell, so these responses
may depend on its entire setting string. The source's convex-hull model
reduces a linear functional to deterministic points; permutation symmetry
makes the assignment of parties to cells immaterial. These interpretation
steps are source-based mathematical explanations, not additional Lean theorems.

## Gap

The preregistration's literature check reads the v2 open-problem statement,
INSPIRE record 2079044 and seven citing records, with full-text searches of
2303.02127, 2407.12347, 2409.08490 and 2305.10587, and the search seat's
reading of 2607.23574. None of those readings supplied a proof for $m>2$.
The recorded MathDB queries are `nonlocality depth` and `Bernards Gühne`.
These are orchestrator- and search-seat-reported, bounded searches in #12316;
they establish no worldwide novelty or priority claim.
Pinned Mathlib supplies the pointwise CHSH bound, finite reindexing and
cardinality identities, rather than the source's full weighted hybrid claim.

## Route

Encode setting 1 by `false` and setting 2 by `true`. The weight
$|x|$ is `hammingDist x (fun _ => false)`; no duplicate weight definition
is needed. Put $s(h)=(-1)^{1+\lfloor(h+1)/2\rfloor}$ and
$t(h)=(-1)^{\lfloor h/2\rfloor}$, so $s(h+1)=t(h)$.
The integer units `ℤˣ` encode exactly $+1$ and $-1$.

Distributing $|x|+|y|$ over the marked coordinates gives

$$F_n(A,B)=\sum_{c=1}^n T_c.$$

Fix the marked setting to `true`. The remaining cell sizes are $r,s\ge1$
and $r+s=n-1$. Split off one Boolean coordinate in each remaining cell.
For each fixed pair of tails, the four terms have phase coefficients
$s(h+1),s(h+2),s(h+2),s(h+3)$, hence form a CHSH expression after local
sign changes. `CHSH_inequality_of_comm`, applied after casting integers to
reals, gives absolute value at most 2. There are $2^{r+s-2}$ tail pairs,
so $|T_c|\le2^{r+s-1}=2^{n-2}$. Summing proves the upper bound.
`Fin.consEquiv.sum_comp` and `Fin.insertNthEquiv.sum_comp` perform the
setting reindexings; the weight distribution and all normalizations are
local proof steps of `result`.

The responses $A(x)=t(|x|)$ and $B(y)=t(|y|)$ attain the bound.
For each pair of tail weights, the four terms sum to 2, as checked by the
four phase residues; every marked-coordinate contribution attains
$2^{n-2}$ simultaneously. `IsGreatest` records both membership of the
bound in the attainable-value set and the universal upper bound.

## Falsifier

A falsifier would give $k,m\ge2$ and unit-valued responses $A,B$ with
$F_n(A,B)>n2^{n-2}$, or show that the bound is not attainable.
`result` excludes both possibilities for the encoded functional.
Singleton cells fall outside its hypotheses; changing the coefficient,
phase, setting count or distinct-permutation convention changes the problem.

## Evidence

The public declarations are exactly `phase`, `hybridValue`, `claim` and
`result`. The sole theorem is `result : claim`; all proof helpers are local.
The module imports pinned Mathlib only and has no frozen D5 prerequisites.
The standard axiom closure is `propext`, `Classical.choice`, `Quot.sound`.
Its Scribe mirror displays each complete definition and quantifier, and its
`Proved` resolution node links this dossier to the frozen settling theorem.
Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

Tier 1: an explicitly published quant-ph open problem whose source proves
$m=2$ and reports numerical checks through 20 parties.
Resolution: `Proved`. Admission basis:
`open-problem-resolution (#12316; Proved)`.
The sole theorem has `proof_shape: bind-only`, `escape_witness: none`.
Utility is `none`: the result is a uniform theorem over all cell sizes and
all deterministic responses, not a bounded enumeration, checker,
numerical reduction or certified finite instance.

### What the settlement shows

- **Proved in this module:** the exact sharp bound for every $k,m\ge2$.
  Its decisive mechanism is a sum of $n$ two-cell CHSH bounds; the explicit
  pair of response functions attains all $n$ contributions together.
  The statement covers all party numbers, including the source's
  conjectured $m>2$ range. No relaxed size hypothesis is asserted.
- **Proved inside the result's proof:** the marked-coordinate decomposition,
  two-cell estimate for nonempty remaining cells, and phase-table attainment.
  These are local proof steps, not separately retained theorems or escape witnesses.
- **Computed:** exhaustive singleton-cell maxima are $(3,1):20$,
  $(4,1):48$, $(5,1):112$, exceeding the proposed values 16, 40, 96.
  The command below enumerates all four singleton response functions $B$;
  for each $B$, independent choices of $A(x)$ give the exact sum of
  absolute row values. Thus it also optimizes over every $A$.
  These readings are integer computations, not new kernel theorems.
- **Open outside this formal assertion:** when the marked coordinate belongs
  to a singleton cell, its remaining cell is empty and the two-cell CHSH
  step has no coordinate to split off there. The computed failures show
  that dropping $k,m\ge2$ does not preserve the conjectured bound.
  A uniform sharp formula for singleton-cell models is not proved here.
- **Open:** whether and under which size hypotheses this decomposition
  gives sharp bounds for hybrid models with three or more cells.
  No such model or theorem is added to this module.
- **Source implication; formal transfer open:** the two-cell classical-bound
  conjecture in Section V is settled. The source's quantum optimizations,
  white-noise thresholds and claims about nonlocality-depth certification
  retain their stated hypotheses; their operator and hybrid-model reductions
  are not checked in Lean by this module. No new values for them are asserted.

```sh
python3 - <<'PYTHON'
from itertools import product
for k in (3, 4, 5):
    strings = list(product((False, True), repeat=k))
    maximum = max(sum(abs(sum(
        (sum(x) + int(y)) * (-1)**(1 + (sum(x) + int(y) + 1)//2) * b[int(y)]
        for y in (False, True))) for x in strings)
        for b in product((-1, 1), repeat=2))
    print((k, 1), maximum, (k + 1) * 2**(k - 1))
PYTHON
```

## ASSUMED-UNVERIFIED

Absence of another published settlement outside the searched sources and
worldwide priority are unverified. The kernel verifies the encoded
integer functional, not the authenticity of the external paper or the
source-to-model interpretation. The convex-hull and permutation-symmetry
transfer, the singleton-cell computations, and the source's applications
are not additional kernel-checked conclusions of this module.
