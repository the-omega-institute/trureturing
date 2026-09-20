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
