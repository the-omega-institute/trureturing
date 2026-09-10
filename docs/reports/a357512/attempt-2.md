# A357512 attempt 2

A is now proved by `fourth_dvd_of_odd_not_three`; hot-tree Lean verification
returns EXIT=0. Repository delivery gates remain to be completed. The proof
does not consume any prime lemma or any external proof source. All attempt-1
definitions and proofs are retained; only its preparatory digest/comment are
updated to reflect the new A theorem.

Skill: `lean4`. Producer: Codex implementation seat, single agent; no independent
review or consensus claimed. Starting commit: `4b1a9ba824` on `lane/math/a357512`.
The user reopens only A: every odd natural `n` with `3 ∤ n` satisfies
`n^4 ∣ a(n-1)`. B remains excluded by the named A17.2 admission conditions in
the preceding report. No B reproof, upstream-code import, or upstream contact
is authorized or planned.

## Search and proposed witness

The complete existing A357512 module was read, including its private lemmas.
Its general `sum_factorization` is the starting point. The original 122 lines
are retained. Repository search with `rg` for `A357512`, `A357513`, Apéry,
binomial congruences, and squared binomial products finds no composite target.
The public surface of `A375178Supercongruence` was read: its only theorem is
a prime-index binomial-cube congruence, with no general summation helper.
The pinned Mathlib search finds `Data/Nat/Choose/Lucas.lean`, concerning
congruences modulo a prime, and no A357512 theorem. These are bounded search
results, not an exhaustive-search claim. Further third-party checks follow.

Proposed A witness before new probes: a denominator-cleared whole-sum identity
or congruence for the reduced sum, valid also at nonunit indices, yielding its
second factor `n^2` after cancelling only constants coprime to `n` (2 and 3).
The prime induction's cancellation of `k` cannot be extended to composites;
attempt 1 already records kernel counterexamples to that intermediate claim.
The stopping criteria are the user's A proof and delivery, a kernel witness
refuting A, or a concrete failed Lean goal and sharper remaining subclaim.

## Nonclaims

No proof of A, new finite-case progress, counterexample, freeze, coverage, PR,
CI success, or novelty is claimed at this checkpoint. No theory volume or atom
will be created. Unopened external pages are `ASSUMED-UNVERIFIED`.

## Fresh external and numerical checks

GitHub REST code searches `A357512 language:Lean`,
`"reducedSum" "choose" language:Lean`, and
`"Apéry" "congruence" language:Lean` each return zero results with
`incomplete_results=false`. Each response has 55 bytes and SHA-256
`4af480b8ee5b87b369a76c49bd22c9a783908272ebffbe97898f8ab0f0772a5f`.
The preceding attempt's read arXiv papers remain bounded negative evidence;
their recorded statements do not cover A. No new external Lean hit was found.

`https://oeis.org/search?q=id:A357512&fmt=json`: HTTP 200, 2499 bytes,
SHA-256 `6a642473a60423ea755db62d0b7a702f3024bcedaaa5345e94de4ab04dbbcbba`.
Python integer arithmetic again matches all 17 DATA entries. In odd
`3 ≤ n ≤ 139`, all 46 nonmultiples of 3 pass and all 23 multiples fail.
The six composites 25, 35, 49, 55, 65, 77 pass. These are semantic probes,
not a proof or finite-case progress. The first Python fetch/probe command
failed before DATA comparison because its OEIS fetch produced no file;
curl returned the above HTTP 200 response and the comparison was then run.

`make lean-cache-ensure`: EXIT=0, status `present`, method `none`, project and
Mathlib `warm`, missing Mathlib oleans 0, stamp miss `null`, pin SHA-256
`6c4c682ffba051b5744fe7a75ccc99d7f3b20227b3b026f392f3315be0adaa4e`.

## Sharpened whole-sum route, before Lean verification

Write `c_k = choose(n-1,k) choose(n+k,k)`. The proposed recurrence is
`(k+1)^2 (c_{k+1}+c_k) = n^2 c_k` for `k<n`. Multiplication by
`c_{k+1}-c_k` gives a denominator-free difference of squares. Summation by
parts with the cubic antidifference `j^2(j+1)^2` should yield
`n^2 ∣ 4 Σ j^3 c_{j-1}^2`. A separate binomial identity should yield
`n ∣ j(c_j+c_{j-1})`, and summation by parts for squares should then yield
`n ∣ 6 Σ j^2 c_{j-1}^2`. These two claims would give the stronger
denominator-cleared target `n^4 ∣ 12*a(n-1)` for all positive `n`, followed by
cancellation of 12 under the requested coprimality conditions. These are
proposed general identities, not verified claims at this checkpoint.

Prerequisite lookup found Mathlib's `Finset.sum_range_by_parts` and
`Nat.choose_succ_right_eq`, `Nat.add_one_mul_choose_eq`. Their source statements
were opened. A first search also named a nonexistent `D5/S3/Arithmetic`
directory; that error is not counted as a negative search result.

The two proposed binomial recurrences now pass `lake env lean` in the ensured
hot tree (EXIT=0): `c_step` and `c_step_linear`. Both hold for every `k<n`,
without primality or index invertibility. The linear identity uses the explicit
integer witness `choose(n-1,k)*choose(n+k,k+1)`. Its first proof attempt failed
when `nlinarith` could not multiply a binomial equality by the other factors;
explicit multiplication and rewriting closed that goal. The whole-sum proof
is still outstanding at this checkpoint.

`telescoping_transport` and `reduced_term_telescopes` now elaborate with
EXIT=0. In `ZMod(n^2)`, twelve times each reduced summand equals
`boundary(n,k+1)-boundary(n,k)`, where
`boundary(n,k)=(3*k^2*(k+1)^2-4*n*k*(k+1)*(2*k+1))*c_k^2`.
This identity consumes both general binomial recurrences; no index is inverted.
An initial `simpa` left `2*(k+1)-1 = 2*k+1`; `ring` closes this normalization.
The finite-sum telescoping step and the final coprimality cancellation remain.

The complete sum and coprimality step now pass Lean, EXIT=0. The only failed
sum attempt used `sum_range_sub'`, whose subtraction points in the opposite
direction; the existing `Finset.sum_range_sub` is the exact required lemma.
The final argument proves `n^2 ∣ 12*reducedSum(n)`, cancels 12 using
`Odd n` and `3 ∤ n`, and consumes the original `sum_factorization`.
No finite computation enters the target proof.
