---
slug: kurkov-a340991-convolution-row-recursion
bibkey: kurkov2025a340991
doi: null
url: https://oeis.org/A340991
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.result
---

# Kurkov's universal convolution-row recursion

## Problem

[OEIS A340991](https://oeis.org/A340991), revision 24, gives Mikhail Kurkov's FORMULA conjecture:

> Conjecture: row polynomials are x*R(n,1) for n > 0 where R(n,k) = R(n-1,k+1) + x*R(n-1,1)*R(1,k) for n > 1, k > 0 with R(1,k) = prime(k) for k > 0. The same recursion seems to work for self-convolution of any other sequence. - _Mikhail Kurkov_, Apr 05 2025

The preregistration is [#24109](https://github.com/the-omega-institute/trureturing/issues/24109). The source has no identified DOI, arXiv identifier or journal version; its note is [kurkov2025a340991](../Library/ArithUnits/kurkov2025a340991.md).

For any commutative semiring $K$ and sequence $a:\mathbb N\to K$, set $A(z)=\sum_{j\ge1}a_jz^j$, $T_a(n,r)=[z^n]A(z)^r$ and $P_{a,n}(x)=\sum_{r=0}^n T_a(n,r)x^r$. Set $R_a(1,k)=a_k$ for $k\ge1$ and $R_a(n,k)=R_a(n-1,k+1)+xa_kR_a(n-1,1)$ for $n>1,k>0$. The assertion is $P_{a,n}(x)=xR_a(n,1)$ for every $n\ge1$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Source series has no constant term; positive coefficients are the sequence | `sourceSeries`, `IsSourceSeries` | The coefficient at zero is zero, and every positive coefficient is $a_j$. |
| Coefficient of the $r$-fold self-convolution, including zeroth power | `T` | Uses `PowerSeries.coeff n (A ^ r)` and $A^0=1$. |
| Row contains columns $0$ through $n$ | `rowPolynomial` | Literal finite sum over `Finset.range (n + 1)`. |
| First positive row and positive-column recursion | `kurkovR` | Exact initial values and two recursive summands; commutativity reconciles the printed product order. |
| Every positive row is $xR_a(n,1)$ | `claim`, `result` | Every commutative semiring, every sequence and every $n\ge1$; the source series is constructed, not assumed. |
| Prime sequence and any other sequence | `result` | Primes are one coefficient sequence; no arithmetic property of primes is assumed. |

Row zero and column zero of the array are totalized by zero. These values do not weaken any positive-index source clause. The unused input $a_0$ supplies no premise. The source's $n=0$ row equals $1$ and lies outside the conjectured identity.

## Motivation

The shifted-column recursion separates a final composition part equal to one from a final part at least two. A coefficient invariant expresses this separation without enumerating compositions.

## Gap

The bounded source and literature screen in #24109 found no settlement of this assertion. OEIS revision 24 retains the conjectural label. The recorded arXiv identifier and author searches found no relevant result; MathOverflow and Zenodo searches found no settlement. OpenAlex and Semantic Scholar were rate-limited, MathDB was blocked, and the related classical monographs were not read in full. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Write $B_k(z)=\sum_{j\ge0}a_{j+k}z^j$, using the existing `RecursiveBoundaryRowSeries.tail`. The consumed Mathlib identity `PowerSeries.eq_X_mul_shift_add_const` gives $B_k=a_k+zB_{k+1}$ and $A=zB_1$. The private `kurkov_coeff` establishes the shifted-tail invariant

$$[x^r]R_a(n+1,k+1)=[z^n]A(z)^r B_{k+1}(z)$$

for all natural $n,k,r$. Induction on $n$ splits the polynomial coefficient index into zero and successor cases. Substitution of $B_{k+1}=a_{k+1}+zB_{k+2}$ matches precisely the two array summands. The consumed `source_pow_coeff_succ` identifies $[z^{n+1}]A^{r+1}$ with $[z^n]A^rB_1$, and `source_pow_coeff_zero` gives zero when the degree is less than the power. The consumed `row_as_of_fn` and `row_coeff` apply `Polynomial.ofFn` coefficient identities to the source's finite-sum row. Polynomial extensionality then proves `result`.

## Falsifier

A sequence, commutative semiring and positive row failing the equality would contradict `result`. A finite successful test alone does not establish the universal equality. Changing the source constant coefficient, dropping commutativity or asserting the equality at row zero changes the statement.

## Evidence

`D5/S1/Recurrence/Algebraic/KurkovConvolutionRowRecursion.result` proves the complete `claim`. The module has `generality: G`, `utility: none` and `admission_basis: open-problem-resolution (#24109; Proved)`. It uses deposit-uncovered with no atom and no cover. All mathematical declarations are symbolic; no finite certificate is part of the Lean proof.

The four-slot escape audit for the sole public theorem `D5.S1.Recurrence.Algebraic.KurkovConvolutionRowRecursion.result` is unfinished under [#25374](https://github.com/the-omega-institute/trureturing/issues/25374). The dependent-family candidate requires faithful source reconstruction, an enrolled readout, a source-law bridge and compiled variation, sensitivity and observational-dependence evidence. No Reg mirror or completed registration is asserted.

### Experiment

The exact integer checker is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/74fe1ca4903771ae85c5df77e18c36d14f15f330/docs/reports/kurkov-a340991), script `docs/reports/kurkov-a340991/check.py`, SHA-256 `457e52407c07a5a9f833e59c1253b4e45ed47c889fda8229b9a2fb79b9079eee`.

The cited bytes were verified with `git -C /Users/auric/trureturing-experiments cat-file -e 74fe1ca4903771ae85c5df77e18c36d14f15f330:docs/reports/kurkov-a340991/check.py`. Executed command: `python3 /Users/auric/.sshx/9771796028dfd23eca1b85de/attempt-1/check.py`; exit $0$. It checks exact integer Cauchy-product rows against the shifted recurrence through $n=10$ for the primes and a signed arbitrary sequence, reproduces prime row $4$ as $[0,7,29,36,16]$ and reports `ALL_CHECKS_OK`. This finite computation is not used in the Lean proof.

## Triage

Tier $1$; resolution `Proved` for the complete preregistered identity.

### What the settlement shows

| Target item | Status and evidence |
| --- | --- |
| Shifted-tail coefficient mechanism, every positive array column and every polynomial coefficient | **Proved, kernel-checked:** the private `kurkov_coeff` invariant, consumed by `result`, quantifies over all natural $n,k,r$ and every sequence over every commutative semiring. |
| Arbitrary commutative-semiring coefficients without positivity, nonzero coefficients, characteristic zero or division; integer and polynomial coefficient semirings included | **Proved, kernel-checked:** `result` quantifies over every `CommSemiring K`; substituting $K=\mathbb Z$ or $K=\mathbb Z[y]$ is within this telescope. |
| Exact prime and signed-sequence check through $n=10$, with prime row $4=[0,7,29,36,16]$ | **Computed:** the experiment entry gives the immutable program, SHA-256, executed command and exit $0$. It is separate from the universal proof. |
| Noncommutative coefficients and variants with a nonzero source constant term | **Open:** neither extension is asserted or proved by this delivery. |

The prime conjecture and its arbitrary-sequence extension are both consequences of `result`. No primality property enters the proof. The source's ordinary coefficient recurrence and displayed finite rows are context; this module settles the conjectured shifted-array identity and does not claim to establish every other assertion in the entry.

## ASSUMED-UNVERIFIED

Literature-screen completeness and absence of a settlement outside the inspected sources remain unverified for the reasons in Gap. The four-slot escape audit is unfinished under #25374; the mathematical theorem does not supply its missing registration evidence.
