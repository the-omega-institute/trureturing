---
slug: alexandersson-jal-quemener-2025-rook-eulerian-interlacing
bibkey: alexanderssonjalquemener2025rook
doi: 10.48550/arXiv.2502.05939
url: https://arxiv.org/abs/2502.05939v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.result
---

# Multiset rook-Eulerian interlacing on Ferrers boards

## Problem

Alexandersson, Jal and Quemener, *Real-rootedness of rook-Eulerian polynomials*,
arXiv:2502.05939v1, Section 3.3, Conjecture 28:

> For Ferrers boards, the polynomial $R(\lambda,\alpha;t)$ is real-rooted.
> Moreover, $R_{\lambda_1}(\lambda,\alpha;t),R_{\lambda_1-1}(\lambda,\alpha;t),\dotsc,R_2(\lambda,\alpha;t),R_1(\lambda,\alpha;t)$ forms an interlacing sequence.

Here $\lambda_1\le\cdots\le\lambda_n$ is the board, $\alpha$ is a vector of
nonnegative integer multiplicities summing to $n$, and $W$ consists of words
with those multiplicities satisfying $0<w_i\le\lambda_i$.
The exponent $\operatorname{asc}(w)$ counts strict adjacent ascents.
Equations (10) and (11) define $R=\sum_{w\in W}t^{\operatorname{asc}(w)}$
and $R_j=\sum_{w\in W,\,w_1=j}t^{\operatorname{asc}(w)}$.
Definitions 8–9 require positive leading coefficients, real nonpositive roots
with multiplicity, equal degrees or one larger degree on the right, and the
chain $\dotsm\le a_2\le b_2\le a_1\le b_1\le0$ for every ordered pair in the
sequence. Issue #12894 specifies nonzero guards for the two refinements.

## Motivation

`D5/S3/Combinatorics/Permutation/MultisetRookEulerianInterlacingRefutation.result`
proves `¬ claim`: the interlacing conjunct fails at $n=6$. The source's other
conjunct, universal real-rootedness of $R$, is not decided by this six-row
result. The companion `MultisetRookEulerianRealRootednessRefutation.result`
refutes that first clause on a positive 120-row board; its separate dossier
is `Problems/alexandersson-jal-quemener-2025-rook-eulerian-real-rootedness`.
The definitions preserve the source word order, strict ascents and root
multiplicity; real-rootedness uses Mathlib's `Polynomial.Splits` directly.

## Gap

Issue #12894 preregisters the Tier 1 named conjecture, its full quantified
statement, the finite-certificate route and a literature screen. That screen
examines the arXiv version record, the arXiv queries `all:"rook-Eulerian"` and
`all:"multiset" AND all:"rook" AND all:"interlacing"`, and MathDB searches for
"rook-Eulerian", "multiset rook" and "Alexandersson Jal"; it records no
settlement in that scope. The primary source states the conjecture in v1.
This is a bounded literature finding, not a claim of worldwide priority.

## Route

Use the board $(3,3,3,3,4,4)$ and content $(2,2,1,1)$. The module checks the
complete sixty-word certificate by kernel reduction of `List.permutations'`,
then computes

$$R_1=2t^4+15t^3+7t^2=t^2(t+7)(2t+1),\qquad R_3=t^3+8t^2+3t.$$

The decreasing roots of $R_1$ are $0,0,-1/2,-7$; those of $R_3$ are
$0,-4+\sqrt{13},-4-\sqrt{13}$. The bottom comparison of $R_3\preceq R_1$
would require $-7\le-4-\sqrt{13}$, contradicting $\sqrt{13}>3$.
No `native_decide`, `sorry` or new axiom is used.

## Falsifier

An incorrect word set, an ascent count different from the strict adjacent
count, either incorrect refined polynomial, or a reversed order in Definition 8
would invalidate this witness. The source's worked example provides an encoding
check: board $22233$, content $(2,2,1)$ gives twelve words and
$t^3+8t^2+3t$.

## Evidence

The kernel-checked public conclusion is the single theorem `result : ¬ claim`.
The certificate equality, refined polynomial evaluations, factorizations,
root multisets and failed bottom comparison occur inside its live proof.

Independent computation command:
`python3 /Users/auric/.sshx/017763f4185f62b04fb3165c/attempt-1/recompute.py`.
It constructs words recursively from the remaining multiplicities and computes
strict adjacent ascents. SymPy 1.14.0 isolates real roots over rational
intervals of width at most $10^{-20}$, retaining multiplicity; polynomial gcd
resolves comparisons at shared roots. It reproduces both the sixty-word
counterexample and the twelve-word source example.

The finite survey deletes zero-content labels in increasing order and replaces
each row bound by the number of surviving labels it admits. This preserves
words, ascents and all comparisons of nonzero refinements. Empty word sets
and zero refinements are omitted. The survey enumerates every positive
composition of $n$ into $k$ parts and every weakly increasing board with entries
in $\{1,\ldots,k\}$, for $1\le k\le n$.

| n | normalized board/content pairs | nonempty pairs | failing pairs |
| --- | ---: | ---: | ---: |
| 1 | 1 | 1 | 0 |
| 2 | 4 | 3 | 0 |
| 3 | 19 | 11 | 0 |
| 4 | 96 | 45 | 0 |
| 5 | 501 | 197 | 0 |
| 6 | 2668 | 903 | 5 |

These are computational findings; the survey and its normalization are not
additional Lean theorems in this module.

## Triage

Tier 1; Refuted under `admission_basis: open-problem-resolution`, issue #12894.
`proof_shape: bind-only`; `escape_witness: none`. The public theorem is the
allowed named-problem settlement, with no companion mathematical declarations.
The utility is `certified-instance` with the typed refutation of `claim`.
Information-escape registration is paused under CLAUDE.md section 3.9.

### What the settlement shows

- **Proved in this module:** the first and last refinements on board $333344$
  separate at the bottom of the chain: $R_3$ has the root $-4-\sqrt{13}<-7$,
  while $-7$ is the least root of $R_1$. This is the mechanism inside `result`.
- **Computed by the command in Evidence:** $R_3\preceq R_2$ and
  $R_2\preceq R_1$, where $R_2=t(8t^2+15t+1)$. Thus adjacent comparisons alone
  do not establish the all-pairs interlacing sequence of Definition 9.
- **Computed by the command in Evidence:** no interlacing failure occurs for
  $n\le5$ in the complete normalized survey. All five failures found at $n=6$
  are between $R_{\lambda_1}$ and $R_1$; the lexicographically first failing
  board is $333344$, with content $(2,2,1,1)$.
- **Computed by the command in Evidence:** the full polynomial at the witness
  is $R=2t(t^3+12t^2+15t+2)$ and is real-rooted.
- **Proved in the literature:** rectangular-board interlacing is covered by
  Ma–Pan, Theorem 1.11, as stated in the primary source, Section 3.3; the present
  nonrectangular witness does not contradict it. Simion's rectangular-board
  real-rootedness also survives.
- **Open:** universal adjacent interlacing; a structural classification of boards and contents admitting
  all-pairs interlacing.
- **Consequence proved by the counterexample:** the authors' all-pairs
  interlacing-sequence method for the distinct-letter case cannot extend
  verbatim to multisets. Theorem 12 for distinct letters is unaffected; using
  the multiset all-pairs conjecture as an intermediate step requires a different
  hypothesis or a different method. This refutation does not negate the
  separate real-rootedness conjecture; the companion first-clause result
  supplies that distinct refutation.

## ASSUMED-UNVERIFIED

The literature search excludes a settlement only within the stated sources and
queries. The finite survey is independently computed, not kernel-verified;
its results beyond the specific witness do not enlarge the public theorem.
The open questions in Triage are not settled by finite agreement.
