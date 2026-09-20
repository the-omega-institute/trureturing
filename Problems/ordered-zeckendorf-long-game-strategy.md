---
slug: ordered-zeckendorf-long-game-strategy
bibkey: bortnovskyi2025ordered
doi: 10.48550/arXiv.2508.20222
triage: theorem
motivation_gids:
  - D5/S0/Conventions/WDigits
  - D5/S1/Digit/Raw
  - D5/S1/Digit/Carry
  - D5/S1/Digit/Normalize
  - D5/S1/Digit/Carry/ListInversions
  - D5/S1/Digit/Carry/RunChainLowerBound
  - D5/S0/Rewriting/NewmanConfluence
  - D5/S0/Rewriting/NormalFormFunction
---

# Optimality of the Ordered Zeckendorf Long Game Strategy

## Problem

A state is an ordered list of Fibonacci numbers. The game starts with `n` copies
of `F_1`. Legal adjacent moves are `(F_i, F_{i+1}) -> F_{i+2}`;
`(F_1, F_1) -> F_2`; `(F_i, F_i) -> (F_{i-2}, F_{i+1})` for `i > 2`;
`(F_2, F_2) -> (F_1, F_3)`; and switching an inversion `(F_i, F_j) -> (F_j, F_i)`
when `i > j`.

The Long Game Strategy uses the priority: all switch moves in any order, combine
adjacent ones from the left, split from the right, then merge from the left.

Conjecture 1.7, quoted from arXiv:2508.20222v2:

> “The LGS has the longest game length.”

Status statement, quoted from the same version:

> “The longest-game strategy described in Conjecture 1.7 is supported by
> empirical simulations. However, a rigorous proof establishing its optimality
> remains an open problem.”

Proposed formalization, after importing the five moves exactly:

```text
∀ n > 0, ∃ g, CompleteLGSRun n g
∀ n > 0, ∀ g, CompleteLGSRun n g ->
  ∀ h, LegalTerminalRun n h -> h.length ≤ g.length
```

Every permitted switch ordering is retained. Switch-order independence is a
proof obligation, not permission to replace the target by a deterministic or
existential variant. Priorities restart after every move, including a switch.

The paper says the conjecture is backed by exhaustive simulations rather than a
proof. In its broader exact game-tree analysis it also states:

> “Due to the combinatorial explosion in the number of game states and legal
> move sequences, a full resolution of the winner for \(n>25\) was
> computationally infeasible.”

That second quote concerns winner computation, not directly Conjecture 1.7, but
it identifies the same state-space obstacle. For length, the paper proves only
upper and lower asymptotics and a structural lemma about repetitions under LGS.

## Motivation

- Erasing order maps a game state to `RawDigits`. Each merge and split move
  preserves Fibonacci value and is closely related to a frozen carry step;
  switch moves erase to the identity.
- The frozen normalizer proves termination and unique canonical output for its
  own oriented carry system. This explains the shared terminal Zeckendorf state,
  but confluence intentionally forgets path lengths.
- The new content is an extremal refinement of rewriting: among ordered
  value-preserving paths from `[F_1,...,F_1]` to the sorted normal form, LGS
  should maximize length.

## Gap

- `OrderedGame.greedy_attainment` constructs the concrete full raw greedy
  continuation, recursively using the strict carry measure, and attains its
  reward `G` at a binary nonadjacent endpoint. This is raw completion, not yet
  ordered completion or domination of all competitors.
- `complete_greedy_reward` proves `w = G c` for every complete
  `RawGreedyPath c e w` with `CanonicalRaw e`. Legal preferred successors are
  unique, so path induction agrees with the recursive concrete continuation.
- `shared_input_merge_repair` proves all five shared-input detours with
  unrestricted spectators, exact endpoints, and exact full reward gains.
  `ones_terminal_promotion` proves ones-first promotion against arbitrary
  terminal raw paths, including interleaved merges. The actual split-prefix cut
  and finite high cascade now discharge the singleton and binary exchange
  cases in `OrderedGame/Optimality.raw_terminal_bound`, proving the full bound
  `weight ≤ G` for every legal path to a canonical raw endpoint.
- `terminal_raw_canonical` proves that actual ordered terminality implies that
  endpoint condition. The remaining bridges are ordered LGS priority erasure
  to `RawGreedyPath` and complete ordered LGS existence for every positive n.
- `OrderedGame` defines ordered legality and the switch move, and
  `path_raw_erasure` proves erasure into a labelled raw path with identical
  accumulated reward. `OrderedGame/Attainment.lgs_move_potential` and
  `lgs_path_potential` prove exact attainment of the inversion potential by
  actual ordered LGS moves and paths. Length optimality remains unproved.
- Newman confluence and normal-form uniqueness say nothing about longest paths.
- LGS contains a tie phrase "switch moves (in any order)".
  `ASSUMED-UNVERIFIED`: an uncommitted exhaustive search over `n <= 16` found
  equal minimum and maximum LGS lengths across all priority-one switch choices.
  If correct, that supports omitting a switch tie-breaker within that range; the
  unrestricted switch-phase independence is now proved by
  `OrderedGame/Attainment.switch_normalization`: all maximal legal zero-reward
  paths share their sorted endpoint and exact inversion length. Complete LGS
  existence and the ordered/raw priority bridge remain open.
- The inversion count now exists here. `D5/S1/Digit/Carry/ListInversions` is
  frozen and supplies `inv : List Nat -> Nat`, its append law, a three-block
  window decomposition, and four local replacement bounds, one per non-switch
  move, stated for arbitrary lists rather than for reachable states. Entries
  may be zero; nothing there assumes positivity.
- The four moves themselves, and their termination, were already frozen under
  a different vocabulary. `D5/S1/Digit/Carry` defines `CarryStep` on
  `RawDigits` with constructors `adjacent`, `double_zero`, `double_one` and
  `double_succ`, which are merge, merge-ones, split-twos and split in
  zero-based indexing, and `D5/S1/Digit/Normalize` proves
  `carryStep_measure_decreases` for every one of them and builds a terminating
  normalizer. A search by the problem's name reaches neither module; a search
  by the name of each operation reaches both.
- The length side now has its first node, and it is a lower bound.
  `D5/S1/Digit/Carry/RunChainLowerBound` is frozen and states that for every
  start `a` and every length `L` there exists a `CarrySteps` chain of exactly
  `L * L / 4` steps out of the raw digit vector carrying one token at each of
  the `L` consecutive indices from `a`. Its proof is a construction rather than
  a pure existence argument: for `L` at least two, one merge at the bottom of
  the run followed by one split for each remaining duplicate carries that run to
  the run of length `L - 2` together with one isolated token in `L - 1` steps,
  and a strong induction in steps of two composes those blocks, with lengths
  zero and one as its bases.
- That module supplies neither a matching upper bound nor a definition of
  `height`, so maximality of the constructed chain is unproved and there is
  still no optimality statement.
- The four `CarryStep` constructors of frozen `D5/S1/Digit/Carry` match the four
  moves of the unordered Zeckendorf game under the index shift `W_i = F_{i+1}`:
  `adjacent` is merging consecutive Fibonacci numbers, `double_zero` is
  combining ones, `double_one` is splitting twos and `double_succ` is the
  general split. Applying arXiv:2009.09510 Theorem 1.2 from an arbitrary start
  rather than from `n` ones remains an external dependency, recorded below.
  Conditional on that transfer, the consecutive-run upper bound reduces to the
  run-length formula of one deterministic strategy, which is a formalizable
  target on its own.

## Route

The weighted split-only subproblem is now proved in
`SplitStabilization.split_prefix_promotion`, `split_phase_promotion`, and
`greedy_split_optimality`. Legal replay preserves the endpoint and does not
decrease full reward; first-overfire supplies the selected split's occurrence.
The comparison covers all complete split phases from arbitrary raw digits,
with ones priority and highest-duplicate priority restarted after every step.
The split-only theorem does not cover paths containing merges.
`OrderedGame/Optimality.raw_terminal_bound` now supplies full weighted raw-game
domination: every legal raw path to a canonical endpoint has reward at most the
concrete `G`, for arbitrary raw starts. Its proof handles interleaved merges via
the actual split-prefix cut, finite high cascades, and exact legal exchanges.
`terminal_raw_canonical` connects actual ordered terminal states to that endpoint
condition. Ordered/raw priority correspondence, complete ordered LGS existence
and complete Conjecture 1.7 remain unproved. Exact ordered potential attainment
and arbitrary switch-phase completion are supplied by `OrderedGame/Attainment`.

1. Use one raw ordered `List Nat`, decoded by `Nat.succ`; multiplicities use
   `Multiset.toFinsupp`. `Carry/OrderedGame` defines all five positional moves,
   their full carry rewards, legal paths, relational LGS and `Conjecture17`.
2. `OrderedGame.path_potential` proves, for every legal finite path,
   `length + inv(decode end) ≤ inv(decode start) + reward`. It reuses the four
   frozen inversion bounds. `path_raw_erasure` preserves the exact reward in
   the labelled raw carrier. `Attainment` proves equality for actual LGS paths;
   comparison still needs the priority bridge. The raw weighted upper bound
   and the ordered-terminal-to-canonical bridge are now proved in `Optimality`.
3. `Carry/SplitStabilization` proves exact site balance, the first-overfire
   least-action bound, unique complete split counts and endpoint, and existence
   of complete split phases. Weighted preferred-split promotion and maximal
   reward among complete split-only phases are also proved.
4. `greedyDecision`, `G`, and `greedy_attainment` now give a concrete full raw
   greedy continuation by the strict carry measure. `ones_terminal_promotion`
   handles arbitrary terminal competitors for the ones-first branch, and
   `shared_input_merge_repair` proves the five duplicated-input merge repairs.
   `split_greedy_terminal_promotion` cuts a genuine complete split prefix before
   the first merge. `raw_terminal_bound` then completes the strict-successor
   induction using all split competitors before handling shared-input merges,
   and strong index descent in the binary branch.
5. Legal cascade replay is proved separately from recognition of a greedy prefix:
   a split at j=a-1 changes the lower boundary, as does a merge at b=a+3.
   `high_cascade` and `Optimality.singleton_merge_cascade` preserve the high
   inputs and reward coordinates under
   those lower-boundary changes. The higher-split,
   lower-split, predecessor and separated-merge exchanges are all Lean-checked.
   Replacement tails need only be legal and terminal.
6. Use exact potential attainment and switch-phase independence to prove
   complete LGS existence, including n=1. Compare every complete LGS run with every terminal
   competitor. No global maximum or unproved Bellman premise is required.

The following older maximum-value proof **sketch** is historical mathematical context; its claims remain
`ASSUMED-UNVERIFIED`. **Nothing here is Lean-verified**, the four move-specific
count calculations are not displayed, and it does not settle the conjecture. Write `inv s` for the inversion
count of a state and `L u` for the longest game length from a sorted state `u`.

- **Decomposition.** `longest s = inv s + L (sort s)`. The easy direction is that
  `inv s` switches bubble `s` into `sort s`. The other direction is induction over
  the move relation: the switch case is an equality because sorting is unchanged
  and `inv` drops by one, and the merge/split case follows from the key lemma
  below together with the Bellman recursion at `sort s`.
- **Key lemma.** Let a merge or split act on an adjacent pair of `s` with values
  `(a,b)`, giving `t`; let `t'` be the result of the same-valued move applied at
  the leftmost such pair of `sort s`. Then `inv t <= inv s + inv t'`. Each of the
  four move kinds reduces to two monotonicity steps on the counts
  `#{p in prefix : p > j}` and `#{q in suffix : q < j}` plus one absorption using
  that prefix and suffix are disjoint parts of the same multiset. The lemma
  mentions no Fibonacci number and no reachability: it holds for arbitrary lists,
  exhaustively over every list of length at most six on values one to six.
- **Consequence.** Every switch is an optimal move, with
  `longest s = longest t + 1`. So LGS priority one is exactly optimal, and the
  conjecture reduces to the sorted case.

**Position is no longer part of the problem.** On a sorted state the prefix
lies at or below the smaller window value and the suffix at or above the larger
one, so only the new window entries can form inversions with the surroundings.
Writing `c_v` for the multiplicity of `v`, the inversions created by each move
are then exact counts: `c_{i-1} + c_i - 2` for a split at `i > 2`, `c_2 - 2`
for a split of twos, `c_{a+1} - 1` for a merge at `a`, and `c_1 - 2 - k` for
the merge of ones whose window starts after `k` other ones. Only the last
depends on position, and it strictly decreases in `k`, so the leftmost
merge-ones is the unique best merge-ones, strictly so whenever more than one is
available. The other three do not depend on position at all. Conditional on the
proposed decomposition, these inversion formulas would settle the positional
choices, and they give "combine adjacent ones from the left" a mechanism: the
leftmost choice keeps the most inversions.

**The remaining problem is a position-free recurrence.** Substituting those
four counts and eliminating the merge-ones position parameter turns the
sorted-state longest length into a recurrence on multisets alone:

```text
L(M) = 0 when no branch applies, otherwise 1 + max over applicable branches of
  merge-ones (c_1 >= 2)          : (c_1 - 2)           + L(M - 2*{1} + {2})
  split-twos (c_2 >= 2)          : (c_2 - 2)           + L(M - 2*{2} + {1,3})
  split i    (i > 2, c_i >= 2)   : (c_{i-1} + c_i - 2) + L(M - 2*{i} + {i-2,i+1})
  merge a    (c_a, c_{a+1} >= 1) : (c_{a+1} - 1)       + L(M - {a,a+1} + {a+2})
```

Conditional on the same decomposition, the following four guarded Bellman
equalities would suffice for Conjecture 1.7, one per region of the LGS priority,
the four regions being disjoint. Necessity over all multisets is not
established:

- `c_1 >= 2` implies the merge-ones branch attains the maximum;
- `c_1 <= 1` and some `i > 2` with `c_i >= 2` implies the branch at the largest
  such `i` attains it;
- `c_1 <= 1`, `c_2 >= 2` and no such `i` implies the split-twos branch attains
  it;
- all multiplicities at most one and non-terminal implies the merge at the
  smallest available `a` attains it.

Two formulations recorded here earlier were stronger than necessary, and both
were false as stated. Branch values below are quoted as inner maxima, excluding
the move itself; a total continuation length is one larger.

- "Any split with index above two is optimal" is false. On the sorted state
  `(3,3,4,4)` the split at 3 has inner maximum 5 while the split at 4 has 7; the
  same failure occurs on `(1,3,3,4,4)` and on `(1,1,3,3,4,4)`. The correct rule
  selects the largest splittable index, which on a sorted state is exactly the
  rightmost splittable pair, so the paper's "splits, starting from the right"
  is a genuine rule rather than an artefact of presentation.
- "Split-twos dominates every merge" is false without the guard. The state
  `{2,2,3,3,7,8}`, which has `n = 2F_2 + 2F_3 + F_7 + F_8 = 65` and is
  reachable from 65 ones by building each block separately, has total
  continuation length 7 through split-twos and 8 through a merge. Its certificate is `L(2,5) = 0`,
  `L(1,1,5) = 1`, `L(4,4) = 1`, `L(2,3,4) = 2`, `L(1,1,3,4) = 3`,
  `L(1,2,2,4) = 4`, `L(1,3,3,3) = 5`, `L(2,2,3,3) = 7`. Only the guarded form,
  in which split-twos is taken when no higher split exists, survives. The
  mechanism is that an independent merge elsewhere can still be followed by the
  optimal higher split, whereas taking split-twos first has already given up a
  move; local independence preserves that loss rather than repairing it.

## Falsifier

A complete certificate consists of a smallest `n`, an exact legal terminal LGS
run `g`, and another exact legal terminal run `h` with `length h > length g`. If
switch ordering changes LGS length, two LGS runs with unequal lengths falsify
the universal proposed formalization even if one remains globally maximal.

## Evidence

Construct a memoized exact DAG for `n <= 30`:

1. canonicalize states only by the ordered Fibonacci-index tuple; do not
   quotient by multiplicity;
2. compute exact `height(S)` and retain a maximizing successor witness;
3. enumerate every LGS tie choice and compare its length to `height(start_n)`;
4. emit, for each state reached by LGS, whether its chosen move is
   height-maximizing;
5. when a priority exchange first fails locally, save both suffix paths even if
   the global conjecture still holds.

This extends the paper's simulation into proof-certificate-shaped data and
directly probes the formal ambiguity.

Measurements taken so far are recorded with their sampling domains, because two
of the claims corrected above were first believed on the strength of a domain
too small to contain their counterexamples.

Over every reachable sorted state with `2 <= n <= 20`: the position-free
recurrence agrees with the original definition at all 797 states; the four exact
inversion counts hold in 5064 of 5064 move windows; the leftmost merge-ones is
optimal among merge-ones in 550 of 550 states, strictly so in 451 of them; and
the merge at the smallest index is optimal among merges in 585 of 585 states, of
which 276 have merges at two or more distinct indices.

Reachable states are still the wrong domain for the domination claims, since
the recurrence is defined on every multiset. The `n <= 20` cutoff misses the
`n = 65` split-twos counterexample entirely; the split-at-3 counterexample
`(3,3,4,4)` has `n = 16` and does lie inside that range, but only above
`n <= 13`, which is where these claims were first believed. Over 14978 arbitrary
multisets of length at most eleven with entries at most thirteen: merge-ones
dominates merge in 1576 of 1576 instances, dominates split-twos in 188 of 188,
and equals the best split in 1294 of 1294; the best split dominates split-twos
in 1377 of 1377 and merge in 10454 of 10454. On that same domain the four
guarded equalities hold in 1776, 10356, 429 and 1957 instances respectively.
Unguarded split-twos against merge fails in 56 of 1749 instances, which is how
the `{2,2,3,3,7,8}` family was found independently of the analysis predicting
it.

Write `U(M)` for the length of the longest chain of carry steps out of the raw
digit multiset `M`, and `run a L` for the multiset carrying one token at each of
the `L` consecutive indices from `a`. The readings below are enumeration on the
domains stated with them.

Over `a` in 1 to 6 and `L` in 1 to 13, `U(run a L)` equals `floor(L^2 / 4)` in
78 of 78 instances, with no observed dependence on `a`. For the proposed
equality over all consecutive runs, the lower bound is the frozen module cited
in the gap above and the upper bound remains open.

All union readings below place the first run at start `a = 1` in zero-based raw
indices, and a gap counts the empty indices between consecutive runs.

Over 684 unions of runs whose gaps are all at least two, being 108 two-run
states with lengths in 1 to 6 and gaps in 2 to 4 together with 576 three-run
states with lengths in 1 to 4 and both gaps in 2 to 4, `U` of the union equals
the sum of `floor(L_i^2 / 4)` in 684 of 684 instances. Over the 100 states of
the same shape with every gap equal to one, that sum is exact in 10; among the
36 two-run members of that sample the measured `U` is above the sum in 30
instances, equal in 6 and below in none.

Within the 81-pair gap-one sample with `L_1` and `L_2` in 1 to 9, the measured
excess over the additive sum is zero when `L_1` is one and `ceil(L_2 / 2)` when
`L_1` is at least two, in 81 of 81 instances. Applying
that correction once per gap is not sufficient: over the 64 three-run states
with lengths in 1 to 4 and both gaps one it is exact in 52, and each of the 12
failures has middle length exactly one and first length at least two, with the
measured `U` above the prediction. Those samples suggest that a run block emits
a token into the empty index above the run, adjacent to a length-one middle run,
so that the two can merge and reach the next gap; that is a reading of the
sample, not a classification of `U`.

Two routes to the upper bound are closed by counterexample, so that the next
attempt need not repeat them.

A potential of the form `sum_i v(m_i) + sum_{i<j} w(|m_i - m_j|)` is excluded by
the following algebra, which is written out here and is not kernel-verified.
Requiring it to equal `floor(L^2/4)` on every run determines it: independence of
the start forces `v` constant, length one forces `v = 0`, and the lengths then
force `w(d) = 1` for odd `d >= 1` and `0` for even `d >= 2`, leaving `w(0)`
free.
That is the statement that `floor(L^2/4)` counts the pairs of run indices at odd
distance. Every member of that calibrated family rises on the step
`(2,4,6,6) -> (2,4,4,7)`: both sides carry exactly one pair at distance zero, so
the `w(0)` term cancels, while the pairs at odd distance go from none to three.
The rise is therefore 3 whatever `w(0)` is, and no member of the family
decreases on every step. For `w(0)` in `{0,1}` the same family is not even an
upper bound: it gives at most 1 on `(0,0,2)`, whose longest chain has length 2.

Splitting `U` over components of the support joined at a fixed distance also
fails. On `(0,0,1,1,6,6)` enumeration gives `U = 6` against a component sum of
`5` at each of the thresholds 1, 2, 3 and 4, its support splitting the same way
at all four. Over random multisets of length 2 to 7 with
entries at most 12 that have at least two components, exact splitting holds in
2634 of 3750 at distance 1, 2976 of 3338 at distance 2, 2594 of 2658 at distance
3 and 1832 of 1835 at distance 4; Whether some larger distance would restore exact
splitting was not tested, and the reason separated runs are additive above is
not established here.

The published strategy, in contrast, attains `U` on every state sampled: over
the runs with start in 0 to 3 and length in 1 to 11 it is exact in 44 of 44, and
over 3000 random multisets of length 2 to 7 with entries at most 9 it is exact
in 3000 of 3000. On runs with start 1 and length `L` in 2 to 14 the
recorded lengths satisfied `greedy(L) = (L - 1) + greedy(L - 2)`, with lengths
zero and one as bases. That this recursion sums to `floor(L^2/4)` is the parity
argument already carried by the frozen module's own proof. Whether the recursion
itself holds for every run is an unverified proof obligation.

None of the enumeration above is a proof. The kernel-verified
material cited in this section comprises the chain-length lower bound and its
recurrence arithmetic in `D5/S1/Digit/Carry/RunChainLowerBound`.

## Triage

`theorem`. Weighted raw domination, legal cascade extraction, ordered terminal
canonicality and exact sorted attainment are now supplied. The remaining route
requires ordered/raw priority correspondence, complete ordered LGS existence
and the final universally quantified comparison. Related suppliers were contributed
in merged PRs #7495, #7575, #7643 and #7651; this work does not replace them.

## ASSUMED-UNVERIFIED

- All permitted switch orders in complete LGS have equal length remains unproved.
- The paper's game moves correspond cleanly enough to frozen carry identities to
  reuse value proofs.
- The at-most-one-repetition lemma suffices to close every local optimality
  branch.
- Whether Conjecture 1.7 was resolved after arXiv v2 is unverified; novelty of
  the exchange-lemma route is unassessed.
- The stronger raw terminal upper bound is kernel-checked in
  `OrderedGame/Optimality.raw_terminal_bound`; the complete source conjecture
  still requires the ordered priority and existence bridges.
- `U(run a L) = floor(L^2 / 4)` is an enumeration reading on `a` in 1 to 6 and
  `L` in 1 to 13, and the union-of-runs readings hold only on the domains stated
  with them. Independence from `a`, the gap-one closed form and the cascade
  explanation are all unproved outside those samples. Of the run-length claims
  only the lower bound is kernel-verified.
- The calibration of the pairwise potential, the identity between
  `floor(L^2/4)` and the count of odd-distance run pairs, and the exclusion it
  yields are written-out algebra with no frozen GID behind them.
- Cusenza et al.'s Lemmas 2.2 and 2.3 explicitly allow arbitrary starting game
  states. The remaining transfer gap is ordered, state-dependent reward, not
  arbitrary-start scope. No Lean formalization of that weighted transfer is
  supplied by the unordered theorem or the historical enumerations.
- The smallest-merge case carries an external dependency this entry does not
  discharge. The unordered Zeckendorf game's longest length is treated in
  arXiv:2009.09510, whose Theorem 1.2 reads "The longest game on any `n` is
  achieved by applying split moves or combine 1's (in any order) whenever
  possible, and, if there is no split or combine 1 move available, combine
  consecutive indices from smallest to largest", and whose Lemmas 2.1 to 2.3
  are each stated "starting from any game state". Two features of that theorem
  match measurements above that were taken independently of it: that split and
  combine-ones may be applied in any order matches the observed equality
  between the merge-ones branch and the best split branch, and "smallest to
  largest" matches the smallest-merge rule. The theorem concerns the unordered
  game only, and transferring it to the ordered length requires identifying the
  two on states whose multiplicities are all at most one, which is not
  established here.
- The bibliography of arXiv:2508.20222v2 cites a different paper by an
  overlapping author group, "Winning strategy for multiplayer and multialliance
  Zeckendorf games". Citation by author surname alone is ambiguous between the
  two; the identifier above is the one meant here.
