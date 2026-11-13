---
slug: nathanson-2026-problem3-lattice-root-bound
bibkey: nathanson2026latticesumsets
doi: 10.48550/arXiv.2607.20571
url: https://arxiv.org/abs/2607.20571v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Additive/NathansonLatticeRootRefutation.result
---

# Nathanson's Problem 3: the exact lattice diameter root bound

## Problem

Melvyn B. Nathanson, *A problem on sumset sizes of sets of lattice points*,
arXiv:2607.20571v1, Problem 3, asks:

> Let $N(h,k)$ be the smallest positive integer such that
> $\mathcal R_{\mathbf Z}(h,k)=\{|hA|:A\subseteq[0,N(h,k)],\ |A|=k\}$,
> and let $N_n(h,k)$ be the smallest positive integer such that
> $\mathcal R_{\mathbf Z}(h,k)=\{|hA|:A\subseteq[0,N_n(h,k)]^n,\ |A|=k\}$.
> Prove or disprove $N_n(h,k)\le N(h,k)^{1/n}$.

The full quantified assertion concerns every integer $h,k\ge2$ and every
positive integer $n$. Here $hA$ permits repeated summands, and
$\mathcal R_{\mathbf Z}(h,k)$ ranges over every $k$-element integer set.
The interval and cube contain integer lattice points, with inclusive endpoints.
Both diameters are the actual least positive integers covering the entire
range. The root is an exact nonnegative real root, without a ceiling.
The surrounding lattice-range theorem fixes the integer-coordinate
interpretation of the cube. The original TeX and its source locator are in
`Library/FiniteGeometry/nathanson2026latticesumsets.md`.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Ordinary repeated $h$-fold sums of every $k$-element integer set | `integerRange h k`, using `nsmulRec h A` |
| Inclusive integer lattice cube $[0,D]^n$ | `cube n D : Finset (Fin n → ℤ)` |
| Equality with the entire integer cardinality range | `intervalCovers h k D` and `cubeCovers h k n D` |
| Least positive covering diameters | `N` and `Nn`, defined by `Nat.find`; positivity belongs to the covering predicates |
| Existence of both minima | Existential proof arguments in `claim`, constructed at the counterexample |
| Every $h,k\ge2$, every $n\ge1$, exact real-root inequality | All binders and the `Real.rpow` expression in `claim` |
| Refutation of the full assertion | `result : ¬ claim` |

## Motivation

The designated settling declaration is
`D5/S3/Arith/Additive/NathansonLatticeRootRefutation.result`, with
`admission_basis: open-problem-resolution` under
[preregistration #29804](https://github.com/the-omega-institute/trureturing/issues/29804).
The external Tier 1 target is the complete original Problem 3.
The counterexample has $(h,k,n)=(2,3,2)$; it negates the universal claim.

## Gap

The exact root bound fails at genuine minima:
$\mathcal R_{\mathbf Z}(2,3)=\{5,6\}$, $N(2,3)=3$, and $N_2(2,3)=2$.
The proposed inequality would require $2\le\sqrt3$.
Attaining the two cardinalities alone would not suffice: the proof also
classifies the entire integer range, proves equality of both bounded ranges
with it, and excludes every smaller positive diameter.

The four-slot registrations of `interval_minimum` and `cube_minimum` remain
unfinished under
[#29804, linked exception](https://github.com/the-omega-institute/trureturing/issues/29804#issuecomment-6842467603).
Their compiled registrations are `declared_unresolved`, with
`IE-C050 ClosedTruthReadout`, `reason=unclassified_form`,
`rule=source.observation_data`. A faithful accepted source-observation
classification and its binding evidence are missing. No completed audit is
claimed for either theorem. The successful `range_two_three` registration
and all three compiled Reg registrations are retained; the designated `result`
is exempt from this registration obligation.

## Route

Sort an integer triple as $a<b<c$. Its six unordered repeated pair sums
can collide only through $a+c=2b$, so their cardinality is five or six.
The sets $\{0,1,2\}$ and $\{0,1,3\}$ realize the two values in $[0,3]$.
Every triple in $[0,2]$ is $\{0,1,2\}$ and misses cardinality six.
This proves the full interval covering property and its leastness.

In the square of diameter two, the line
$\{(0,0),(1,0),(2,0)\}$ realizes five and the triangle
$\{(0,0),(1,0),(0,1)\}$ realizes six. Kernel-checked finite enumeration
proves that every triple in this square has one of these cardinalities.
Every triple in the integer unit square has six pair sums, so diameter one
misses five. Positivity excludes zero. This proves the square covering
property and its leastness.

These coverings supply existence proofs for `Nat.find`; the leastness
theorems identify the resulting values independently of the proof arguments.
Specializing the universal claim then gives $2\le\sqrt3$, contradicted by
nonnegativity of the square root and $4>3$.

## Falsifier

A defect in the complete range classification, either equality of ranges,
either leastness argument, or the exact-root specialization would invalidate
this counterexample. These are separate obligations in the Lean proof.
Real-point cubes, restricted sumsets, noninclusive endpoints, and a rounded
root are different assertions and receive no settlement claim here.

## Evidence

The module's public surface contains seven definitions and four theorems:
`range_two_three`, `interval_minimum`, `cube_minimum`, and `result`.
The corresponding Scribe contains all eleven public nodes and one typed
Refuted `OpenProblemResolutionClaim` on `result`. Its Blueprint Markdown
is produced by the canonical emitter.

All eleven authored D5 theorems, including the seven private helpers, have
the conservative `proof_shape: bind-only` classification. Each helper is
consumed by the settling proof. No escape witness or general content credit
is claimed. The sole module admission basis is the external named-problem
resolution. Compiled axiom closures use only `Classical.choice`,
`Quot.sound`, and `propext`; the utility evidence identifies the closed
negation of the literal `claim`.

The retained source-bound `range_two_three` registration is
`declared_validated`, with evidence identity
`812f6839a1cb14f7f72ac779947d154042bce47357ccf9fc048b7887c8871434`.
The two minimum registrations retain the unfinished boundary in Gap.

## Triage

### What the settlement shows

| Item | Result and boundary |
| --- | --- |
| Original universal Problem 3 | Refuted by `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.result` |
| Complete range at $(h,k)=(2,3)$ | Proved as `range_two_three`: exactly $\{5,6\}$ |
| Genuine interval and square minima | Proved as `interval_minimum` and `cube_minimum`: three and two, with attainment and leastness |
| Failure mechanism | The unit square cannot realize a three-term progression and hence misses five; its next integer diameter is two, already greater than $\sqrt3$. This explains the proved minimum calculation. |
| Rounded bound at this counterexample | The proved values satisfy $2=\lceil\sqrt3\rceil$. This numerical consequence gives no universal rounded-bound theorem. |
| Successor candidate | Unresolved: for every $h,k\ge2$ and $n\ge1$, do the same genuine minima satisfy $N_n(h,k)\le\lceil N(h,k)^{1/n}\rceil$? Existence, literature screening, and a proof or counterexample remain necessary; no new research unit is started here. |
| Other source statements | The equality of unrestricted integer and lattice ranges is compatible with this bounded-diameter counterexample. No other source problem or theorem is settled or invalidated by this delivery. |

### Literature status

The preregistration records inspection of the pinned source through its
references. Its bounded screen includes the returned citing work Henry Shin,
arXiv:2609.01690v1, and the inspected related works arXiv:2610.02216v1,
arXiv:2609.08915v1, and arXiv:2603.15556v4; no exact answer was found in
the inspected text. The Shin interval $[0,N-1]$ convention is not silently
identified with the present inclusive $[0,D]$. MathDB access and challenged
search-engine readings remain missing. These readings establish no global
priority or exhaustive absence of earlier solutions.

## ASSUMED-UNVERIFIED

Literature completeness and absence of every earlier published solution are
`ASSUMED-UNVERIFIED`. The rounded-bound successor is unresolved. The
`interval_minimum` and `cube_minimum` escape registrations remain unfinished
under the linked exception; their Lean theorems remain kernel checked.
