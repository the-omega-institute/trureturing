---
bibkey: abuku2024enforce
authors: Tomoaki Abuku; Shun-ichi Kimura; Hironori Kiya; Urban Larsson; Indrajit Saha; Koki Suetsugu; Takahiro Yamashita
year: 2024
title: Enforce and selective operators of combinatorial games
doi: 10.1007/s00182-024-00910-6
url: https://arxiv.org/abs/2311.01006v2
claim: Problem 42 asks whether ruleset domination implies equality of all enforce nimbers and the dominating ruleset's nimbers.
strata_touched:
  - D5/S0/Certificates/Games/AbukuEnforceNimberDomination
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1007/s00182-024-00910-6

Source: https://arxiv.org/abs/2311.01006v2

The source is arXiv:2311.01006v2, also published in International Journal of
Game Theory 53, 1249–1273. Page numbers below are the printed arXiv pages.

## Definitions

Definition 4, page 6:

> The ruleset A = (X, f) is short if for any x ∈ X, there exists a non-negative integer T_A(x) such that every play sequence, even ignoring the alternating play condition, starting in x, terminates in at most T_A(x) moves.

Definition 5, page 6:

> Consider a short impartial ruleset A = (X, f). Then O(x) = O_A(x) ∈ {P, N} is the perfect play outcome of the position x ∈ X, under ruleset A.

Definition 10, page 10:

> Let A = (X, f_A) and B = (X, f_B) be short rulesets on a set X. Then A and B are jointly short if the ruleset (X, f) given by, for all x ∈ X, f(x) = f_A(x) ∪ f_B(x), is short.

Definition 13, page 11:

> The enforce operator on these rulesets is the combined ruleset A ⊙ B, where on each turn, before a play, the opponent enforces one of these two rulesets, and the current player plays according to that ruleset.

Definition 14, page 11:

> If, for any x ∈ X, O_{A⊙B}(x) = O_A(x), then ruleset A dominates ruleset B, denoted A ⊢ B.

Definition 28, page 17:

> Let S denote a finite set of non-negative integers. Then the minimal excludant mex(S) is the least non-negative integer not in S.

Definition 29, page 18:

> For any game position x, the nim-value function G(x) is G(x) = mex({G(x′) | x′ ∈ f(x)}).

Definition 33, page 18:

> Let A and B be jointly short rulesets on X, and consider the game A ⊙ B. Then, the enforce nimber of x ∈ X is Gᴱ(x) = Gᴱ_A⊙B(x) where Gᴱ(x) = mex({Gᴱ(x′) | x′ ∈ f_A(x)} ∩ {Gᴱ(x′) | x′ ∈ f_B(x)}).

The mex of an option-value set is its least missing nonnegative integer.

## Problem 42

Page 23, Section 8:

> If a ruleset dominates another, does it also ‘nimber dominate’ that ruleset? That is, does it follow that all nimbers of the combined ruleset are the same as those of the dominating ruleset?

The formal statement uses an arbitrary type X, option sets fA and fB, a
uniform finite bound on each play from a fixed starting position, two P/N
outcome functions, and two natural-valued functions satisfying Definitions
29 and 33. Domination is pointwise equality of the outcome functions.
The proposed implication concludes pointwise equality of the nimber functions.

## Scope

The three-position refutation has fA = (∅, {0}, {0,1}) and
fB = (∅, {0}, {0}). Both outcome functions are (P,N,N), while
the nimber functions are (0,1,2) and (0,1,1).
This does not refute the source's outcome-level domination results.

Literature completeness is ASSUMED-UNVERIFIED. The literature screen in
https://github.com/the-omega-institute/trureturing/issues/19251 covers the
source, publisher record and the later works listed there; citation discovery
is incomplete and the Odawara thesis and enforce-operation talks are unread.
