---
bibkey: bortnovskyi2025ordered
authors: Ivan Bortnovskyi and Michael Lucas and Steven J. Miller and Iana Vranesko and Ren Watson and Cameron White
year: 2025
title: The Ordered Zeckendorf Game
doi: 10.48550/arXiv.2508.20222
claim: The Long Game Strategy is conjectured to achieve the greatest length among all legal terminating plays of the ordered Zeckendorf game.
strata_touched:
  - D5/S1/Digit/Carry
  - D5/S1/Digit/Normalize
  - D5/S0/Rewriting/NewmanConfluence
  - D5/S0/Rewriting/NormalFormFunction
license: citation-only
triage: anchor
---

# The Ordered Zeckendorf Game

Bortnovskyi, Lucas, Miller, Vranesko, Watson, and White study a variant of the
Zeckendorf game whose states are ordered lists of Fibonacci numbers, with
combine, split, and inversion-switch moves. Their Conjecture 1.7 states that the
Long Game Strategy attains the longest game length; the paper reports that this
is supported by exhaustive simulation but that a rigorous optimality proof
remains open. It also records that a full resolution of the winner was
computationally infeasible beyond `n = 25`.

This note is the literature anchor for the problem candidate
`Problems/ordered-zeckendorf-long-game-strategy.md`.

## Source scope

The source is arXiv:2508.20222v2, originally posted 2025-08-27 in `math.NT`.
The DOI above identifies the version-independent arXiv record. A journal
publication was not established in the recorded source checks.

The research intake registered in #9018 reports bounded checks of the current
arXiv history, exact-title and ordered-longest searches, and OpenAlex W4414447583;
no later exact resolution was verified in that scope. This is not a worldwide
priority claim. The v2 conjecture remains the full implementation target.

## Direct weighted comparison

With positive paper indices, write c_i for multiplicity. The full reward of a
carry followed by sorting is c_1-1 for combining ones, c_2-1 for splitting twos,
c_(i-1)+c_i-1 for splitting i>2, and c_(a+1) for merging a,a+1. The carry itself
is included. In raw indices the single ordered representation is `List Nat`
with named decode `List.map Nat.succ`; n raw zeros represent n source ones.
The new `D5/S1/Digit/Carry/OrderedGame.path_potential` proves the natural-number
inequality `length + inv(decode end) ≤ inv(decode start) + sum carryReward`
for every finite legal ordered path, using the existing local inversion bounds.
Its position-aware LGS relation retains all switch choices and restarts priority
after every move. `Conjecture17` is the full, still unproved target, including
existence of a complete LGS run for every positive n.
`path_raw_erasure` now maps every ordered path to a labelled raw path with
identical accumulated reward, removing switches and retaining the existing
`CarryStep` relation for each labelled carry and its spectator context.

`D5/S1/Digit/Carry/SplitStabilization` proves complete split-phase existence,
exact site balance, a first-overfire least-action bound, and uniqueness of both
firing counts and endpoint. Its notion of stability means binary multiplicities;
it permits consecutive occupied indices and therefore is not game terminality.
The weighted extension proves legal preferred-split promotion through lower
prefixes, promotion in every complete phase using first-overfire, and
`greedy_split_optimality`: every complete greedy split phase maximizes full
reward among complete split phases from the same arbitrary raw start. Ones
take priority; otherwise the highest duplicate is recomputed after each split.
This comparison excludes merges and does not yet establish full-game optimality.

The remaining proof candidate uses strict-successor induction on the existing
carry measure, with greedy continuation cost rather than a global maximum.
Preferred promotion and greedy comparison for complete split-only phases are
now proved. The remaining comparison must handle interleaved merges and the
five shared-input merge detours.
For singleton inputs, the high block C_a;S_(a+2);...;S_r advances one duplicate
through a binary tail, fills the preceding holes and has reward one per move.
A lower preferred split can be extracted across this block. Prefix recognition
and legal replay require different hypotheses: at j=a-1 the lower split changes
c_a, although the replay's high input and reward coordinates remain valid.

At a binary state let a be the least enabled merge and b>a a competing merge.
If c_(b-1)=1, C_b can be replaced by C_(b-1);S_(b+1), gaining one and reducing
the competing index. Otherwise b≥a+3 and its high cascade commutes with C_a.
At b=a+3 the lower merge changes c_(b-1), so legal replay must allow that boundary
change. Each replacement must have a legal common endpoint; its tail need not
be greedy. Induction applies after a strict first successor, never at the state
whose optimality is being proved. These merge exchanges, exact sorted
attainment and all-switch completion remain unproved in Lean.

Cusenza et al., *Bounds on Zeckendorf Games*, arXiv:2009.09510v1, Theorem 1.2
and Lemmas 2.1–2.3 concern unordered maximal move counts; the lemmas explicitly
allow arbitrary starting states. They do not account for paid ordered switches.
Bond–Levine, *Abelian Networks I*, arXiv:1309.3445, supplies the classical
least-action comparison, not these state-dependent reward inequalities.
The direct weighted candidate is a research deduction attributed to the #9018
intake, not a theorem claimed from either paper. Existing repository carry,
termination, inversion and chain suppliers from PRs #7495, #7575, #7643 and
#7651 retain their attribution. No complete conjecture resolution is claimed.

## Verified locator

- arXiv: https://arxiv.org/abs/2508.20222
- DOI: https://doi.org/10.48550/arXiv.2508.20222
