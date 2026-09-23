---
slug: mi-xu-yang-2025-partially-restricted-stack-maximal-sort-refutation
bibkey: mixuyang2025partialstacks
doi: 10.54550/ECA2025V5S3R22
url: https://ecajournal.haifa.ac.il/Volume2025/ECA2025_S2A22.pdf
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.result
---

# Mi-Xu-Yang Conjecture 5.2 refutation

## Problem

Mi, Xu and Yang, ECA 5:3 (2025), Article #S2R22, introduce the stack
machines used in the conjecture. Printed page 1 states:

> The map sends permutations through a stack that always avoids the permutation
> 21 when read from top to bottom.

> We further generalize s to s_{(T,k)}. We define the maps s_{(T,k)} that avoid
> containing more than k distinct permutations from T in the stack at once.
> More specifically, the map sorts a permutation π via the following stack
> sorting algorithm: If adding the leftmost element of the input to the stack
> keeps the stack (T, k)-avoiding, push that element into the stack. Otherwise,
> pop the top element off the stack and append it to the output.

Printed page 2 defines containment and avoidance:

> Given two permutations π and σ, we say π contains σ if there exist
> a_1, a_2, . . . , a_k such that the sub-permutation
> π_{a_1} π_{a_2} . . . π_{a_k} is order-isomorphic to σ. Otherwise, we say π
> avoids σ.

> Furthermore, for a set T of permutations and a nonnegative integer k, we say
> π is (T, k)-avoiding if π contains at most k elements of T.

The same page fixes the second map:

> Throughout the paper, we use t to denote s_{({12,21},1)}.

Printed page 6 defines the sorting time:

> Let m_{(s∘t)}(π) be the smallest nonnegative integer j such that
> (s ∘ t)^j(π) = id_{|π|}.

Printed page 7 gives the proved sufficient direction:

> Lemma 5.5. For n ≥ 3 and π ∈ S_n, if π = 2σ1n where
> σ ∈ Av_{n−3}(213) then m_{(s∘t)}(π) = 2n − 5.

It then states the named open assertion:

> Conjecture 5.2. The permutation π takes 2n − 5 sorts to be sorted to the
> identity by (s ∘ t) if and only if π = 2σ1n and
> σ ∈ Av_{n−3}(213).

The formal reading takes the quantifier to be `n ≥ 3`, reads
`m_{(s∘t)}(π) = 2n−5` as `TakesSorts π (2n−5)`, and reads
`π = 2σ1n` with `σ` a permutation of `{3,…,n−1}` avoiding 213. The printed
conjecture carries no lower-bound clause; the `n ≥ 3` reading is taken from
Lemma 5.5 and Conjecture 5.1 and was preregistered in issue #9318. The reading
uses `s := s_{({21},0)}`, the page-1 West machine. Figure 1 on printed page 1
shows a different restricted map and supplies no evidence about `t`.

## Motivation

At `n = 3`, every nonidentity permutation is sent to the identity by one
application of `s ∘ t`. The printed extremal form supplies only `213` at this
length. In particular, `π = 132` has sorting time `1 = 2*3−5` but cannot have
the form `2σ1 3`, so it refutes the only-if direction of Conjecture 5.2. Issue
#9318 preregistered the literal conjecture, its full quantifiers, this
counterexample, and the literature check before the kernel probe.

## Gap

The source proves Lemma 5.5 but does not prove the converse asserted by
Conjecture 5.2. The repository's frozen
`D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.s` is the same West map by
definition, but its private well-founded recursion cannot be evaluated by the
kernel from another module: `decide +kernel`, `rfl`, `unfold s; rfl`, and
`simp [s]` all fail on `s [3,2,1] = [1,2,3]`. The formalization therefore
defines the paper's `s_{({21},0)}` instance directly, as preregistered in
#9318.

The corrected issue #9318 literature check records Crossref
`is-referenced-by-count` 0. OpenAlex has record `W6969488267` for DOI
`10.54550/eca2025v5s3r22`, with `cited_by_count` 0 and creation date
2025-10-10; `filter=cited_by:W6969488267` returned zero works. A title search
found no arXiv version, and three MathDB queries found no entry. Semantic
Scholar returned HTTP 429 and is `ASSUMED-UNVERIFIED`. These bounded readings
do not establish exhaustive literature coverage or publication priority.

## Route

Define the paper's stack operation directly from finite lists, and define
`TakesSorts` as reaching `List.range' 1 pi.length` at iterate `j` while every
earlier iterate differs from it. Kernel evaluation gives the `n = 3`,
`π = 132` instance. Specializing `claim` at that instance forces
`LemmaForm 3 [1,3,2]`; normalization of its leading entry gives a
contradiction.

The public theorem has `proof_shape: bind-only`: its live proof path consists
of finite kernel decisions, specialization, iff projection, and normalization.
It introduces no non-bind-only intermediate proposition, so
`escape_witness: none`. Its preregistered admission basis is
`open-problem-resolution` under issue #9318.

## Falsifier

The counterexample is `n = 3`, `π = 132`. It would fail if `t 132` were not
`321`, if `s 321` were not `123`, if an earlier zero-th iterate were already
the identity, or if `132` had the form `2σ1 3`. The sibling permutations
`231`, `312`, and `321` are counterexamples for the same reason: each takes one
sort, and at `n = 3` the middle word `σ` is empty, so `213` is the only
permutation of the form `2σ13`; none of the three is `213`.

## Evidence

- Lean theorem:
  `D5/S1/Words/Patterns/MiXuYangPartiallyRestrictedStackMaximalSortRefutation.result`.
- Freeze event:
  `sha256:a86068464a4e64324cf2a3772e564954fc9cdc758073af2513ffa60e0926db19`.
- Module statement identity:
  `sha256:a14d73039847bed93545159f6ec8114dd9bd16cae5912c1eec0f24c2b234011a`.
- Result declaration identity:
  `sha256:4adcfc445cd7f34bb49612780bfa2dd72648876acefdc90673be08c554aa212e`.
- The Freeze event has no project-level frozen prerequisites. The sole import is
  pinned Mathlib's `Mathlib.Data.List.Sublists` module.
- The axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.
- Kernel `S_3` table for `t`: `123→321`, `132→321`, `213→132`,
  `231→312`, `312→123`, `321→123`.
- Kernel `S_3` table for `s`: `123→123`, `132→123`, `213→123`,
  `231→213`, `312→123`, `321→123`.
- Consequently `s∘t ≡ 123` on `S_3`; `123→0` sorts and every other
  permutation takes one sort.
- The issue #9318 computation for `n = 4, 5, 6, 7` found no further failure:
  the permutations attaining `2n−5` sorts were exactly the `2σ1n` forms,
  with counts `1`, `2`, `5`, and `14`.
- That Python implementation was checked against Theorem 4.1, Corollary 4.1,
  Lemma 3.1, Lemma 5.5, and Conjecture 5.1 before its Conjecture 5.2 sweep.
- The quoted displays were checked against rendered printed pages 1, 2, 6,
  and 7 of the DOI-linked PDF.

## Triage

`theorem`; first-tier external named conjecture, preregistered in issue #9318.

| proof_shape | escape_witness | utility | admission_basis |
| --- | --- | --- | --- |
| bind-only | none | certified-instance/refutes | open-problem-resolution |

The result refutes Conjecture 5.2 exactly under the preregistered `n ≥ 3`
reading. It does not assert Conjecture 5.1, does not reassert Lemma 5.5 as a
new theorem, and does not assert the restricted repair obtained by changing
the range to `n ≥ 4`. There is no atom and no digestion coverage edge.

## ASSUMED-UNVERIFIED

Semantic Scholar coverage, exhaustive literature coverage, and publication
priority are `ASSUMED-UNVERIFIED`. The bounded `n = 4..7` computation does not
prove the `n ≥ 4` repair. Source-to-Lean fidelity, proof-shape classification,
and the interpretation of `2σ1n` are semantic review judgments; the Lean
kernel checks the formal statement and proof, not their equivalence to the
cited prose.
