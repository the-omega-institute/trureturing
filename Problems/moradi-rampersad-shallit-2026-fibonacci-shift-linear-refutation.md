---
slug: moradi-rampersad-shallit-2026-fibonacci-shift-linear-refutation
bibkey: moradi2026fibonaccilinear
doi: 10.48550/arXiv.2603.21645
url: https://arxiv.org/abs/2603.21645v1
triage: theorem
motivation_gids:
  - D5/S0/Automata/BinaryZeckendorfLanguage
  - D5/S0/Automata/TypedPartialDFAO
  - D5/S1/Words/ZeckendorfBeattyBridge
---

# Moradi–Rampersad–Shallit Problem 1: shifted Fibonacci–Thue–Morse state complexity

## Problem

Delaram Moradi, Narad Rampersad, and Jeffrey Shallit, *Complexity of Linear
Subsequences of Fibonacci-Automatic Sequences*, arXiv:2603.21645v1,
Section 4, [Problem 1](https://arxiv.org/html/2603.21645v1#Thmproblem1):

> Prove the number of states in a minimal automaton generating
> (t(i+c))ᵢ≥₀ is Θ(c).

This dossier anchors only that complete statement. Put F₀ = 0, F₁ = 1 and
Fₙ₊₂ = Fₙ₊₁ + Fₙ. For an MSD-first word x = x₀…xₗ₋₁ over {0,1}, set
val(x) = Σⱼ<ₗ xⱼFₗ₊₁₋ⱼ, with val(ε) = 0. Valid words contain no adjacent
ones; arbitrary leading-zero padding is valid. The value t(n) is the parity
of the number of occupied digits in the canonical Zeckendorf representation
of n.

For c ∈ ℕ, s(c) is the attained minimum number of live states of a finite
deterministic partial MSD automaton with Boolean state outputs. Every
counted state is reachable. The start state is counted and has a zero
self-loop; a rejecting sink is omitted. For every binary word x, the output
of the partial run is some(t(val(x)+c)) when x is valid and none otherwise.
Thus every valid padded word is covered, including ε and all-zero words,
which output t(c). Invalid execution is undefined, rather than an output
chosen without a constraint. These conventions follow Sections 2.1 and 2.2
of the source.

The full eventual uniform proposition is

$$
\exists a,b\in\mathbb R,\quad a>0\land b>0\land
\exists c_0\in\mathbb N,\quad
\forall c\in\mathbb N,\quad c\ge c_0\Longrightarrow
ac\le s(c)\le bc.
$$

The exact Lean definition is
`D5/S1/Digit/ZeckendorfProblem1Refutation.Problem1`.
Requiring c₀ ≥ 1 gives the same eventual statement, since the threshold can
be replaced by max(c₀,1). The settling theorem
`D5/S1/Digit/ZeckendorfProblem1Refutation.problem1_refuted : ¬ Problem1`
negates the entire proposition with this original machine class.

## Motivation

The source's Theorem 14 gives an O(c) upper bound and asks whether a uniform
linear lower bound also holds. The frozen binary Zeckendorf language,
partial output-machine interface, and canonical Fibonacci arithmetic
provide the source domain and construction machinery. The number of raw
arithmetic windows alone does not establish the number of distinct complete
continuation behaviors.

## Gap

Tier 1: a recent explicitly numbered external open problem, preregistered
before the mathematical probe in
[issue 11703](https://github.com/the-omega-institute/trureturing/issues/11703).
The source v1 labels the statement open. The issue's literature reading
found no resolution in the checked exact-author and Fibonacci-shift arXiv
queries, Shallit's papers page, or the inspected adjacent primary papers.
This is `not-found-in-searched-scope`, not worldwide absence or a priority
claim. The Springer edition, thesis, and citation limits below remain
undischarged; the settlement is expressly of arXiv v1 Problem 1.

## Route

The raw window retains canonical parity and occupation of the least
Fibonacci digit at both endpoints. Its arithmetic expansion determines
the complete Option-valued residual on every continuation, including
malformed ones. A canonical-support carry barrier supplies the boundary
control needed for contextual replacement at shifts c = F_H.

For H ≥ 14, the legal fourteen-digit MSD blocks
`B0 = 00010010101000` and `B1 = 00010101001000` have equal complete residuals
inside arbitrary legal high and low context when the replaced block lies
within the final H digits. Every actual residual first receives a legal
representative of length H+7. Replacing B1 by B0 strictly decreases its
fixed-length binary rank without changing its complete residual. A least-rank
representative therefore avoids B1 in the final H digits.

A conditional weighted count retains the entering and final bits of each
legal block; it assumes no independence between blocks. With
φ = (1+√5)/2 and δ = 1−φ⁻¹⁴, the B1-avoiding legal H-digit words number at
most φ^(H+1) δ^⌊H/14⌋. The seven leading digits contribute a factor at most
128. Finite residual realization constructs a reachable partial machine
in the exact source class, giving

$$
s(F_H)\le 128\varphi^{H+1}\delta^{\lfloor H/14\rfloor},
\qquad
\frac{s(F_H)}{F_H}\le
128(2\varphi+1)\delta^{\lfloor H/14\rfloor}
\quad(H\ge14).
$$

The proof establishes 0 ≤ δ < 1 and unbounded positive shifts F_H. For any
positive a and any threshold c₀, it chooses H with F_H ≥ c₀ and the displayed
ratio strictly below a. This contradicts the uniform lower-bound conjunct
and literally refutes the full Θ(c) statement. A subsequence suffices here
because every proposed eventual lower bound quantifies over all shifts.

## Falsifier

The refutation would fail if contextual replacement lost a legal suffix
output or changed undefined invalid execution; if a residual were omitted
from the bounded representative cover; if rank descent changed word length
or legality; if the conditional count omitted an entering bit, a boundary,
or a legal word; if realization introduced a counted sink, dropped padding,
or lacked the initial zero-loop; or if the family were bounded or its ratio
did not tend to zero. These obligations are discharged in the source chain
used by `problem1_refuted`. No finite computation is used to infer a
uniform result.

## Evidence

The ten authored theorems in the eight-owner source chain are
`source_word_coordinates`, `source_expansion`, `window_residual_congruence`,
`lower_support_carry_barrier`, `contextual_replacement`, `all_state_cover`,
`finite_residual_realization`, `normalized_state_cover`,
`uniform_avoidance_count`, and `problem1_refuted`. Their canonical owners
are the corresponding `D5/S1/Digit/ZeckendorfRawWindow`,
`ZeckendorfCarryBarrier`, `ZeckendorfContextualReplacement`,
`ZeckendorfResidualCover`, `ZeckendorfResidualMachine`,
`ZeckendorfResidualNormalForm`, `ZeckendorfAvoidanceCount`, and
`ZeckendorfProblem1Refutation` modules.

The exact final declaration has type `¬ Problem1`. Its proof also establishes
attainment and positivity of s(c), the source-class machine witnesses, and
the unbounded-family estimates above. The Lean axiom closure of these ten
theorems contains only `Classical.choice`, `Quot.sound`, and `propext`.
The argument uses no `sorry`, new axiom, assumed separator, or assumed
quotient law. The mathematical evidence is the compiled source chain;
finite research observations do not carry this conclusion.

## Triage

`theorem`. The full external Problem 1 statement is refuted.
`admission_basis: open-problem-resolution`, with preregistration #11703.
Against the protected baseline the necessary new chain has substantive
arithmetic, complete-residual construction, and counting content;
`proof_shape: content`. No additional bind-only companion result is claimed.

### What the settlement shows

- [proved: D5/S1/Digit/ZeckendorfProblem1Refutation.problem1_refuted]
  The positive uniform eventual linear lower bound fails. The proof's
  unbounded Fibonacci-shift family has s(F_H)/F_H → 0. The mechanism is a
  contextual collision of complete partial residuals, followed by an
  exhaustive cover by legal words avoiding a fixed block; a raw-window
  count cannot supply the conjectured lower bound.
- [proved: D5/S1/Digit/ZeckendorfResidualMachine.finite_residual_realization]
  Every shift still admits a finite reachable partial MSD machine correct
  on every valid padded word and undefined on every invalid word. The
  attained minimum is positive, as established inside `problem1_refuted`.
- [literature-attested: arXiv:2603.21645v1, Theorem 14]
  The O(c) upper bound is compatible with this refutation. The general
  upper-bound statements of Theorems 13 and 15 concern separate bounds;
  this theorem does not refute them or the paper's results for the Fibonacci
  word. They are not reproved by this delivery.
- [open]
  Sharp state complexity for arbitrary shifts, conditions supporting a
  linear lower bound on restricted shifts, and the optimal rate along the
  Fibonacci family are not settled here. No logarithmic bound for this
  parity sequence is inferred from the source's different Fibonacci-word
  sequence or an LSD-first convention.

## ASSUMED-UNVERIFIED

The conclusion is tied to arXiv:2603.21645v1. The subscription-only DLT
chapter, DOI 10.1007/978-3-032-28404-4_14, has not been inspected to determine
whether it changes Problem 1. Direct retrieval of Moradi's April 2026 thesis
returned a bot challenge; the advisory locator Problem 3/p.58 is unverified.
The second citing work reported by Springer remains unidentified. None of
these limitations is treated as negative search evidence or as a Lean
premise. Novelty and priority beyond the searched scope are unverified.

The quoted problem and adapted machine conventions are attributed to
Moradi, Rampersad, and Shallit's arXiv v1, licensed CC BY 4.0. The explicit
quantified model and refutation are repository adaptations. That license
is not attributed to the uninspected Springer edition or thesis.
