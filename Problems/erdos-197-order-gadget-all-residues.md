---
slug: erdos-197-order-gadget-all-residues
bibkey: kasel2026erdos197
doi: null
url: https://arxiv.org/abs/2609.02939v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ErdosGrahamOrderGadget.result
---

# The Order Gadget of the Erdős–Graham Two-Set Problem Is Infeasible at Every Scale

## Problem

William Kasel, *Structural rigidity in the Erdős–Graham two-set permutation problem*,
arXiv:2609.02939v1, Remark 30:

> The full order gadget is nevertheless conjectured infeasible at every M ≥ 16 (machine-verified for
> 16 ≤ M ≤ 200 and M = 512, Proposition 18); at every swept scale with M ≢ 0 (mod 8) the C3 core was
> satisfiable, and other attack subsets were observed computationally to take over (Proposition 19);
> a proof beyond the swept scales would need per-residue analogues of Theorems 27–28 built from the
> same flood toolkit.

The order gadget OG(M) of Definition 15 asks for a linear order of `(M, 2M]` in which no in-block
three-term arithmetic progression is monotone and, for `x ∈ {15, 16}` and `1 ≤ j ≤ x/2`, the guard
`2M + 2j − x` precedes the bottom `M + j`.

## Motivation

The frozen theorem `D5/S3/Combinatorics/ErdosGrahamOrderGadget.result` proves the conjecture: for
every `M ≥ 16` the gadget is infeasible. The paper needed only the residue class `M ≡ 0 (mod 8)`,
which contains the dyadic scales, to eliminate the canonical partition for Erdős Problem 197. The
all-scale statement is a local obstruction usable by any block-based attack on that problem, and it
settles the remaining seven residue classes.

## Gap

Issue 9614 records the screen made before the work. The erdosproblems.com problem page, forum thread
and proof-claims page for Problem 197 show no proof claims and nobody working on it; the author's
repository still lists the full conjecture as open; google-deepmind/formal-conjectures states only
the parent problem; searches by title, arXiv number and "order gadget" found no later proof. Nothing
under `Problems/`, `D5/` or `Library/`, and no entry of the three screening records, concerns this
paper.

## Route

Write `b_j = M + j`, `t_i = 2M − i`, `h = 3M/2`. AP-freeness gives the four midpoint rules of the
paper, from which follow its zigzag lemma (on any ladder of a fixed difference, one parity class of
rungs precedes all its neighbours), phase dichotomy, and the phase-independent flood: for a center
`q` and a class `C` of step `g ∈ {2, 4}` with `q ≡ C + g/2 (mod g)`, one relation `q ≺ v` with `v`
in the admissible mirror range forces `q ≺ w` for every class member `w` in that range.

**Even `M`.** Use the four guards `t_11 ≺ b_2`, `t_7 ≺ b_4`, `t_14 ≺ b_1`, `t_10 ≺ b_3`. Split on
the order of the adjacent tops `t_11, t_10`; this fixes which parity leads on the difference-one
ladder. In each branch let `c` be the largest integer below `h` in a fixed class modulo four and
`d = c + 2`. A difference-two flood from `c` reaches a top, a guard carries it to a bottom, and a
difference-four flood from `c` seeded at that bottom reaches `d`: `c ≺ d`. The same four moves from
`d`, with the other two guards, give `d ≺ c`.

**Odd `M`.** The same scheme with the guards `t_13 ≺ b_1`, `t_9 ≺ b_3`, `t_12 ≺ b_2`, `t_8 ≺ b_4`,
splitting on `t_13, t_12`, with centres `c = M + j + 2 + 4⌊(M − 2j − 5)/8⌋` and `d = c + 2`.

In both parities every seed distance, radius and mirror is an explicit function of `M`, valid for all
`M ≥ 16` (even) and `M ≥ 17` (odd) with no exceptional small cases. The theorem follows because each
four-guard set is a subset of the fifteen guards of OG(M).

## Falsifier

The statement would fail if some scale admitted an AP-free order satisfying either four-guard set.
It would also fail to be the paper's statement if the guards were read with `j` ranging up to `x`
instead of `x/2`, or with the block closed at `M`; the definitions in the formal module follow
Definition 15 literally, with the block `M + 1, …, 2M`.

## Evidence

An independent SAT encoding (explicit transitivity, CaDiCaL) reproduces Proposition 18 and the
residue behaviour of the three-guard core at `16 ≤ M ≤ 40`, and finds each four-guard set
inconsistent with AP-freeness at every `M` from 16 to 168 of the matching parity and at 200, 201,
256 and 257. No guard set of size at most four is inconsistent at every `M` from 24 to 168 at once,
which is why the argument splits by parity. Every intermediate relation of both hand proofs was
checked mechanically at every even `M` from 16 to 120 and every odd `M` from 17 to 121, each flood in
both phases of its ladder and without the guards installed.

## Triage

`theorem`; Tier 1 named open conjecture from a 2026 paper, preregistered in issue 9614 before the
work. The computational use is `none`: the delivered statement is universally quantified over every
`M ≥ 16`, and no declaration is a bounded enumeration, a checker, a numeric reduction or a certified
instance.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources named above; citation indices were not exhaustively
reachable, so no worldwide priority claim is made. The result settles Kasel's conjecture on the order
gadget; it does not settle Erdős Problem 197 itself.
