---
slug: peltomaki-2020-silver-slope-abelian-periods
bibkey: peltomaki2020abelianperiods
doi: 10.1016/j.jnt.2020.04.007
url: https://arxiv.org/abs/1905.06138
triage: theorem
motivation_gids:
  - D5/S1/Words/Mechanical/SilverSlopeAbelianPeriods.result
---

# Peltomäki's silver-slope abelian period set conjecture

## Problem

J. Peltomäki, *Abelian periods of factors of Sturmian words*, Journal of Number Theory 214 (2020),
251–285, arXiv:1905.06138v3, Conjecture on page 283:

> Let $\alpha = [0; \overline{2}]$. The abelian period set of a Sturmian word of slope $\alpha$ is $\mathcal{Q}^+_\alpha \cup \mathcal{M}_\alpha$.

An abelian period set comprises the minimum abelian periods of all nonempty factors.
For $\alpha=\sqrt{2}-1$, let $q_0=1$, $q_1=2$ and $q_{k+1}=2q_k+q_{k-1}$.
The asserted set is $\{q_k:k\geq0\}\cup\{2q_k:k\geq0\}\cup\{q_k+q_{k-1}:k\geq1\}$.

## Motivation

`D5/S1/Words/Mechanical/SilverSlopeAbelianPeriods.result` proves the unconditional equality
`silverAbelianPeriodSet = silverCandidateSet`. The definitions use Boolean Parikh vectors,
proper coordinatewise containment of the head and tail, and nonempty factors of the lower
mechanical word of slope $\sqrt{2}-1$ and intercept zero. The source's common-factor-language
interpretation identifies this language with the factor language of Sturmian words of that slope.
The source denominators are encoded by $q_k=P(k+1)$ and $q_{k-1}=P(k)$.

## Gap

Preregistration issue #13073 identifies this as a tier-1 published conjecture. Its literature screen
found no settlement in the searched title, conjecture and silver-slope period sources; this is a
bounded negative finding. The paper's upper inclusion and Proposition 5.5 supply known partial
results. Proposition 5.7 supplies a disjunction between the two additional families.

## Route

The Pell error and determinant identities yield uniform integer approximation exclusions.
Explicit head, block and tail counts give factors with periods $2P(k+1)$ and $P(k+1)+P(k)$;
the approximation bounds and endpoint alignment exclude every smaller period.
Singular windows are separated by at least the next Pell denominator. Packing their residue
witnesses gives a length lower bound, which contradicts the block budget for noncandidate periods.
The settling theorem combines this exclusion with realization of all three candidate families.

## Falsifier

A nonempty lower mechanical factor whose minimum abelian period is outside the candidate set,
or a candidate value not realized by any such factor, would contradict the equality.

## Evidence

The settling theorem and the supporting declarations are Lean-kernel checked with axiom closures
contained in `propext`, `Classical.choice` and `Quot.sound`. Every public declaration has a canonical
Scribe mirror. The proved statement has no unproved witness or forward-inclusion hypothesis.

## Triage

`theorem`; settlement of the published conjecture is Proved, under
`admission_basis: open-problem-resolution (#13073; Proved)`.

### What the settlement shows

- Proved in `SilverSlopeAbelianPeriods.result`: the entire silver-slope minimum-period set is
  exactly the three candidate families, with no length or denominator cutoff.
- Proved in `SilverSlopeAbelianWitnesses`: both additional families occur at every index $k\geq1$,
  in separate explicit factors. `silver_w2_min_period` uses length
  $2q_k(q_k+q_{k-1})+q_k-1$ at start $2q_k+q_{k-1}$.
  `silver_wr_min_period` uses length $(2q_k+1)(q_k+q_{k-1})-1$ at start zero for odd $k$,
  and length $(2q_k+1)(q_k+q_{k-1})-2$ at start $q_k+1$ for even $k$.
- Proved in `SilverSlopeAbelianPellArithmetic` and `SilverSlopeAbelianSingularPacking`: the
  decisive mechanisms are the exact signed Pell error, uniform approximation exclusions and
  singular-window separation. The two `UnimodularApproximationBound` theorems retain general
  integer-coordinate hypotheses beyond the particular silver-slope application.
- Computed (probe-reported; `exact_check 5000`): finite enumeration agrees with the candidate
  set through length 5000. This finite reading is separate from the uniform proof.
- Literature result: Proposition 5.7 guarantees that one of $2q_k$ and the adjacent-denominator
  semiconvergent occurs. The delivery proves separate realizations of both values. Identification
  of the paper's particular first-return construction with one of these explicit factors is not
  formalized here.
- Open: the analogous complete period-set equality for constant partial quotients greater than
  two, and sharp minimum lengths of factors realizing each candidate period. No such extension
  or sharpness statement is inferred from the present witness lengths.
- Source consequence: the silver-slope candidate inclusion is an equality. The paper's proved
  upper inclusion and partial realization propositions retain their statements; the delivery
  imposes no new assumption on them and makes no claim to settle its general-slope or k-abelian
  questions.

## ASSUMED-UNVERIFIED

The negative literature result is bounded by the searches recorded in #13073. The finite enumeration
is probe-reported and is not used by the Lean proof. The source's equivalence between mechanical
and arbitrary Sturmian factor languages is literature interpretation, not a new theorem in this
settling module. Information-escape registration is paused under CLAUDE.md §3.9.
