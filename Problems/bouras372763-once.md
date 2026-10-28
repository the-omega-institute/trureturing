---
slug: bouras372763-once
bibkey: bouras2024a372763
doi: null
url: https://oeis.org/A372763
triage: theorem
motivation_gids:
  - D5/S3/Arith/Primes/BourasA372763OnceRefutation.result
---

## Problem

OEIS A372763, COMMENTS (unpaginated), states: "Conjecture 2: Except for 2 and 3, all primes appear in the sequence once."
Its NAME is "Denominator of the continued fraction 1/(2-3/(3-4/(4-5/(...(n-1)-n/(n+5)))))."
The source index range is $n \ge 3$. The source and statement are preregistered in [#18628](https://github.com/the-omega-institute/trureturing/issues/18628).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Inner fraction from $2$ through $n-1$, terminal value $n+5$ | `nested`, `K`, `a` | Right fold with rational division and the literal terminal value. |
| Denominator | `a` | Positive denominator of the reduced rational number. |
| All primes except $2$ and $3$ | `claim` | Natural prime binder and the two explicit exclusions. |
| Appear once in the sequence | `claim` | Unique natural index with $3 \le n$ and $a(n)=p$. |
| Conjecture is false | `result` | Negation of the complete claim. |

The parameter $x$ in `nested` and `K` exposes the source's terminal argument; `a` specializes it to $n+5$. Total rational division and truncated natural subtraction extend the definitions to all natural indices; `claim` restricts the assertion to the source range. There are no additional hypotheses.

## Motivation

The prime $11$ occurs at $n=10$ and $n=21$. Distinct admissible indices disprove uniqueness without a global occurrence classification.
The numerical values are already published in OEIS data and in Bouras, *A New Primes-Generating Sequence*, arXiv:2509.09745v1, Table 2.

## Gap

The exact target is the uniqueness conjecture. A global classification of all occurrences and Conjecture 1 are separate assertions.

## Route

`D5.S3.Arith.Primes.BourasA372763OnceRefutation.result` applies the assumed uniqueness assertion to the prime $11$, using `Nat.prime_eleven`. Kernel evaluation of the two rational denominators gives $a(10)=a(21)=11$; `ExistsUnique.unique` would then imply $10=21$.
The settlement has `proof_shape: bind-only`, `escape_witness: none`, and `admission_basis: open-problem-resolution (#18628; Refuted)`.
The module imports only pinned Mathlib and has no direct frozen D5 dependencies.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Falsifier

A mismatch between the source's continued fraction or index range and the formal definitions, or either computed denominator differing from $11$, would invalidate this settlement's source correspondence.

## Evidence

Kernel evidence is the frozen settling declaration `D5/S3/Arith/Primes/BourasA372763OnceRefutation.result` and its live local evaluations `hten` and `htwentyone`.

The independent finite computation is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/4d3404c32ec26a2d3d54bf1ed150f97bc218a940/docs/reports/oeis-bouras-continued-fraction-occurrence-counts).
From an experiments checkout containing that revision, the command is `python3 docs/reports/oeis-bouras-continued-fraction-occurrence-counts/check.py 300 20000`, exit $0$, final result `RESULT PASS`.
The script SHA-256 is `05b533313a609bd3bf139aef952a062566625488521351d2d2955731427d9ffb`.
Exact nested evaluation, nonzero tails, agreement with the published data and the denominator formula are tested for $3 \le n \le 300$. Occurrence counts use $3 \le n \le 20000$ and primes $p \le 10000$.

## Triage

| Item | Status and evidence | Scope |
| --- | --- | --- |
| Prime $11$ has the two admissible indices $10$ and $21$, refuting uniqueness. | Proved: kernel-checked `result`, using its local evaluations `hten` and `htwentyone`. | Complete binding claim; a single repeated prime suffices. |
| At $n=10$, $D=55$ and $\gcd(D,10!)=5$; at $n=21$, $D=121$ and $\gcd(D,21!)=11$. The fractions have nonzero tails and reduced denominator $11$. | Computed: the experiment entry above, exit $0$, SHA-256 as given. | The two indices are within the exact-evaluation range. The fractions are $72847/11$ and $153407898057891727/11$. |
| Primes $2$ and $3$ occur zero times, $11$ twice at $10,21$, and every other prime at most $10000$ once. | Computed: the experiment entry above, exit $0$, SHA-256 as given. | Only $3 \le n \le 20000$; this is no assertion about later indices. |
| Exact global multiplicity two for $11$ and one for every other prime at least $5$. | Open: no uniform formal proof is delivered. | Unbounded indices. |
| Conjecture 1: every term is $1$ or prime. | Open: this refutation does not prove or disprove it. | Entire sequence. |
| Literature completeness and publication priority. | Open; ASSUMED-UNVERIFIED: the source readings below do not establish exhaustive coverage. | The repeated numerical witness is already published. |

### What the settlement shows

Proved: the uniqueness assertion fails because the same prime denominator survives at two distinct admissible indices. Kernel evaluation in `result` supplies both values.
Computed: for the two witnesses, $D=6n-5$ takes the values $55$ and $121$, while factorial cancellation leaves denominator $11$ in both cases. The finite occurrence window supports a corrected classification with $11$ exceptional.
Open: the unbounded corrected classification, global exclusion of $2,3$, and Conjecture 1 require their own arguments. Any use of Conjecture 2 as a uniqueness hypothesis loses that hypothesis. Assertions about existence of prime occurrences alone are not settled here; consequences for arguments using the conjecture require checking each such argument.

### Literature status

The preregistration records source and literature checks by its Claude Code orchestrator: the OEIS entry, Adamczewski's *OEIS Open* (arXiv:2608.11941), the Epoch OEIS benchmark, the AlphaProof Nexus results, formal-conjectures, and the repository screen. Its searched scope yielded no explicit settlement. Bouras's arXiv:2509.09745v1, Table 2, and the OEIS data already contain the repeated $11$. These are source and literature readings, not a claim of a new numerical discovery.

## ASSUMED-UNVERIFIED

Completeness of the external literature search and any assertion that this formal refutation is unpublished remain ASSUMED-UNVERIFIED. Finite computations do not prove the unbounded corrected classification. The correspondence between the published expression and the formal definitions is source fidelity, rather than a theorem about publication text.
