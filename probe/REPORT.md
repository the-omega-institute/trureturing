# Ayad–Bouchenna Problem 1: isolated probe

Preregistration: issue #8990, read in full before local inspection or computation. Target: for every natural base B ≥ 2 and positive n, n divides the base-B reversal of every positive multiple of n if and only if n divides B² − 1. Visible inputs: the probe brief, its complete GoalArtifact, and issue #8990. No other seat output is an input.

## Predictions registered before testing

1. Definition-level enumeration of all multiples n·t with 1 ≤ t ≤ 4000, for B = 10 and 1 ≤ n ≤ 400, returns exactly {1, 3, 9, 11, 33, 99}, the divisors of 99. This is the source Theorem 3 anchor.
2. For every integer B in [2, 17), the same enumeration returns exactly the positive divisors of B² − 1, with no extra n and no missing divisor in 1 ≤ n ≤ 400.
3. The sparse 0/1-digit construction in the brief never fails for B in [2, 12), n in [2, 60), gcd(n,B) = 1, multiplicative order T ≥ 2, and n not dividing B² − 1: its m is positive, n divides m, and n does not divide its actual base-B reversal.
4. Reversing the least-significant-first natural digit list and evaluating it agrees with direct digit-string reversal for m = 1 through 100000 in each base 2, 3, 10, and 16, including trailing-zero inputs.

Any failure of predictions 1–3, or a source/statement mismatch, ends this probe with the discrepancy reported. Finite success is evidence for the route, not proof of the universally quantified theorem. The Lean probe may contain explicitly identified sorry holes and does not constitute admission or completion of issue #8990.

## Intended mathematical content and verification boundary

The preregistered candidate escape witness is the unbounded statement: if B ≥ 2, n > 0, and n does not divide B² − 1, then there exists a positive multiple m of n whose base-B reversal is not divisible by n. The construction and its live derivation must be checked independently. Predicted proof_shape: content; predicted admission_basis: escape-witness, with preregistered open-problem-resolution as the alternative if upstream reuse makes it bind-only.

The decisive probe will measure the remaining Lean obligations, compiled module wall time and checker time, and explicitly inventory every sorry. No claim of a completed theorem or of an independently repeated literature-open check is made here.

## Step 1: definition-level enumeration

Independent program: `python3 probe/verify.py enumerate`, exit 0. All 24000000 requested multiples were tested, without early termination for failing n. Elapsed time: 7.110848 seconds. Predictions 1 and 2 held.

| B | Passing n (also exactly the divisors of B² − 1) | Extras | Missing |
|---|---|---|---|
| 2 | 1, 3 | 0 | 0 |
| 3 | 1, 2, 4, 8 | 0 | 0 |
| 4 | 1, 3, 5, 15 | 0 | 0 |
| 5 | 1, 2, 3, 4, 6, 8, 12, 24 | 0 | 0 |
| 6 | 1, 5, 7, 35 | 0 | 0 |
| 7 | 1, 2, 3, 4, 6, 8, 12, 16, 24, 48 | 0 | 0 |
| 8 | 1, 3, 7, 9, 21, 63 | 0 | 0 |
| 9 | 1, 2, 4, 5, 8, 10, 16, 20, 40, 80 | 0 | 0 |
| 10 | 1, 3, 9, 11, 33, 99 | 0 | 0 |
| 11 | 1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120 | 0 | 0 |
| 12 | 1, 11, 13, 143 | 0 | 0 |
| 13 | 1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168 | 0 | 0 |
| 14 | 1, 3, 5, 13, 15, 39, 65, 195 | 0 | 0 |
| 15 | 1, 2, 4, 7, 8, 14, 16, 28, 32, 56, 112, 224 | 0 | 0 |
| 16 | 1, 3, 5, 15, 17, 51, 85, 255 | 0 | 0 |

Anchor B = 10: {1, 3, 9, 11, 33, 99}, reproducing the paper’s Theorem 3 within the registered finite window. No universal conclusion is inferred from the enumeration.

## Step 2: source fidelity and reversal

Read the downloaded source with `pdftotext -layout`; the PDF and extracted text remain exclusively in the runner scratch directory, outside this worktree. Printed p. 8 §4.1 defines m*_B by reversing the coefficients of the usual finite base-B expansion, including zeros. Printed p. 8 Proposition 5 gives the divisor-to-property implication. Printed p. 9 Problem 1 asks whether these are the only positive integers. The preregistered quantifiers and biconditional are faithful; no correction is needed.

For m > 0 and B ≥ 2, write the canonical digits as [a₀,…,aₖ] with aₖ ≠ 0. Nat.digits is least-significant-first; Nat.ofDigits evaluates the coefficient at index i with weight B^i. Thus the reversed list evaluates to aₖ + aₖ₋₁ B + … + a₀ B^k, exactly the source formula. If a₀ = 0, it is simply a trailing zero in the reversed coefficient list, so the value has fewer canonical digits without changing this equality. No injectivity or reversal-involution claim for numbers ending in zero is required.

Independent cross-check: `python3 probe/verify.py faithfulness`, exit 0; model of Nat.digits/ofDigits versus reversed positional string evaluated with Python int. Bases 2, 10, 16 use independent built-in string formatting; base 3 uses most-significant-place extraction. Each row tests m = 1 through 100000.

| Base | Values | Trailing-zero inputs | Mismatches |
|---|---|---|---|
| 2 | 100000 | 50000 | 0 |
| 3 | 100000 | 33333 | 0 |
| 10 | 100000 | 10000 | 0 |
| 16 | 100000 | 6250 | 0 |

Prediction 4 held. This Python test checks the stated mathematical model; pinned Lean definitions and the digits reconstruction theorem are inspected in Step 4.

## Step 3: independent proof-route check

There is no mathematical gap detected in the route. The strict inequality m < 2B^s is essential for the leading digit, including B = 2. Taking B^s > n and m = n·ceil(B^s/n) indeed gives B^s ≤ m < B^s+n < 2B^s. If d = gcd(n,B), the property implies d divides m*_B; also d divides B and m*_B is 1 modulo B. Hence d divides 1 and d = 1. This argument does not need choosing a prime factor.

For n = 1, the conclusion and property hold directly. For n > 1, coprimality makes B a unit modulo n with positive finite order T. Order 1 already gives B² = 1. Order 2 also already gives B² = 1 and never enters the nondivisor construction. In the remaining case T ≥ 2, choose the positive representative c of −(1+B) modulo n, choosing n when that residue is zero. The c+2 occupied indices are distinct: 0 and 1 lie below T, and positive multiples iT are distinct. Thus no carries occur, even in base 2, and the highest index is k = cT. Reversal sends these indices to k, k−1, and (c−i)T for 1 ≤ i ≤ c. Modulo n, the forward value is 1+B+c = 0, and the reverse value is 1+B^(-1)+c. Multiplying the latter by B gives 1−B². This avoids needing a field or cancelling a nonunit. If n does not divide B²−1, the reverse cannot be zero modulo n.

The already-published forward implication can also be organized as the list identity R(L) = B^(length(L)−1)·V(L) modulo n when B² = 1; the empty-list case is separate. This is consistent with the paper's even/odd argument and handles trailing-zero input digits.

Exact-integer construction check: `python3 probe/verify.py construction`, exit 0. It evaluates the actual integer m and its arithmetic reversal and independently checks the reversed-exponent formula. Registered prediction 3 held.

| B | Required construction pairs |
|---|---|
| 2 | 28 |
| 3 | 36 |
| 4 | 26 |
| 5 | 40 |
| 6 | 16 |
| 7 | 41 |
| 8 | 25 |
| 9 | 31 |
| 10 | 19 |
| 11 | 40 |

Total 302 pairs, failures 0, largest exponent cT = 3248. Edge stresses over bases 2 through 16 and n ≤ 400: n = 1 in 15 bases; order 1 in 30 pairs; order 2 in 73 pairs; base-2 coprime nondivisor cases 198. The leading-one construction was checked in all 6000 pairs, with 2459 noncoprime pairs each giving a genuine reversal counterexample. These remain finite experimental results, not a replacement for the Lean witness.

## Step 4: upstream and repository reuse

### Counted mathlib searches

- characterisation: `rg -n -i -g '*.lean' 'HasReverseMultipleProperty|reverseBase|reverseB\b|reverse.{0,50}(any|all).{0,30}multiple|multiple.{0,50}revers|\bAyad\b|\bBouchenna\b' .lake/packages/mathlib/Mathlib`; 1 matching lines, exit 0. Positive control: `rg -n -i -g '*.lean' ofDigits .lake/packages/mathlib/Mathlib`; 328 matching lines, exit 0.
- reversal: `rg -n -i -g '*.lean' 'ofDigits_reverse_cons|ofDigits_reverse_zero_cons|digits_ofDigits|digits_append|eleven_dvd_iff' .lake/packages/mathlib/Mathlib`; 26 matching lines, exit 0. Positive control: `rg -n -i -g '*.lean' digits .lake/packages/mathlib/Mathlib`; 681 matching lines, exit 0.
- order: `rg -n -i -g '*.lean' 'orderOf_pos|pow_orderOf_eq_one|orderOf_eq_one_iff|isUnit_iff_coprime|pow_totient' .lake/packages/mathlib/Mathlib`; 162 matching lines, exit 0. Positive control: `rg -n -i -g '*.lean' ZMod .lake/packages/mathlib/Mathlib`; 2813 matching lines, exit 0.

### Counted repo searches

- characterisation: `rg -n -i -g '*' 'HasReverseMultipleProperty|reverseBase|reverseB\b|reverse.{0,50}(any|all).{0,30}multiple|multiple.{0,50}revers|\bAyad\b|\bBouchenna\b' D5 Problems Library Blueprint`; 2 matching lines, exit 0. Positive control: `rg -n -i -g '*' ofDigits D5 Problems Library Blueprint`; 152 matching lines, exit 0.
- reversal: `rg -n -i -g '*' 'ofDigits_reverse_cons|ofDigits_reverse_zero_cons|digits_ofDigits|digits_append|eleven_dvd_iff' D5 Problems Library Blueprint`; 18 matching lines, exit 0. Positive control: `rg -n -i -g '*' digits D5 Problems Library Blueprint`; 3689 matching lines, exit 0.
- order: `rg -n -i -g '*' 'orderOf_pos|pow_orderOf_eq_one|orderOf_eq_one_iff|isUnit_iff_coprime|pow_totient' D5 Problems Library Blueprint`; 34 matching lines, exit 0. Positive control: `rg -n -i -g '*' ZMod D5 Problems Library Blueprint`; 6420 matching lines, exit 0.

Pinned Mathlib commit: db584cd6d46c92f209a44c0f1c829460d327499d. Source inspection confirms `digits` is little-endian and `ofDigits` is its positional evaluation. No whole-statement reuse hit: the one Mathlib characterisation-query hit is affine vector-span prose; the two repository hits are divisibility-support inclusion prose, unrelated to digit reversal. Neighboring repository reversal results concern binary complement recurrences, decimal palindrome squares, or decimal subsequences; none implies the present universal property. No cover route was found.

Reusable upstream declarations, inspected at their definitions:

- `Mathlib/Data/Nat/Digits/Defs.lean`: `Nat.ofDigits_append`, `Nat.ofDigits_reverse_cons`, `Nat.ofDigits_reverse_zero_cons`, `Nat.coe_ofDigits`, `Nat.digits_ofDigits`, `Nat.ofDigits_digits`.
- `Mathlib/Data/Nat/Digits/Lemmas.lean`: `Nat.digits_append_digits` (the actual name, not `Nat.digits_append`), `Nat.digits_append_zeroes_append_digits`, `Nat.digits_length_le_iff`, `Nat.ofDigits_mod_eq_head!`.
- `Mathlib/Data/Nat/Digits/Div.lean`: `Nat.eleven_dvd_iff`, only the decimal alternating-sum test, not this classification.
- `Mathlib/Data/ZMod/Basic.lean`: `ZMod.isUnit_iff_coprime`, natural cast and divisibility bridges.
- `Mathlib/GroupTheory/OrderOfElement.lean`: `orderOf_pos` for a finite group, `pow_orderOf_eq_one`, `orderOf_eq_one_iff`. Apply to the unit in `(ZMod n)ˣ`, not indiscriminately to a nonunit in the multiplicative monoid.
- `Mathlib/FieldTheory/Finite/Basic.lean`: `Nat.ModEq.pow_totient` is an available alternative positive period; no minimality of the period is needed in the sparse argument.

External Lean search capability was tested via the GitHub code-search API: exact identifier `HasReverseMultipleProperty` with `language:Lean` returned total_count = 0; positive control `Nat.digits` in `leanprover-community/mathlib4` returned total_count = 11. This narrow search does not certify absence of every differently named external theorem, nor repeat the issue's literature-open audit.

## Cache preparation for Step 5

The worktree initially had no `.lake`. Ran `make lean-cache-ensure` with the exact PATH required in the brief before any Lake invocation; exit 0. Preparation precedes Step 4 source searches because the pinned Mathlib sources were absent initially. Receipt:

```text
LEAN_CACHE {"status":"seeded","worktree":"/Users/auric/trureturing-op-ayad-reverse","donor":"/Users/auric/trureturing","method":"clonefile","reason":null,"stamp_miss":null,"pin_sha256":"sha256:1499ba00eb44d4b760a213127fc10c82158b7595723ae155179378723cf14db3","clonefile_errno":null,"clonefile_errnos":[],"clonefile_attempts":1,"clonefile_cleanup_error":null,"mathlib_missing_olean_files":0,"mathlib_missing_olean_samples":[],"archive_status":"not_attempted","archive_mode":null,"archive_skip_reason":"project olean state is warm","archive_reason":null,"archive_producer_commit_sha":null,"archive_workflow_run_id":null,"mathlib_olean_state":"warm","mathlib_olean_probe_error":null,"project_olean_state":"warm","project_olean_probe_error":null}
```
