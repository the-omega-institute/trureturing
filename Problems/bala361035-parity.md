---
slug: bala361035-parity
bibkey: bala2023quarticparity
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Arith/FactorialRatio/BalaA361035Parity.result
url: https://oeis.org/A361035
---

# Bala's A361035 parity conjecture

## Problem

Peter Bala's [OEIS A361035](https://oeis.org/A361035) defines
$a(n)=9979200(4n)!/(n!(n+3)!^3)$ and states:

> Conjecture: a(n) is odd iff n = 2^k - 3 for some k >= 2.

The index $n$ is any natural number, including zero.
The prerequisite integrality and the exact exponent bound are part of the source's statement in
[preregistration #18607](https://github.com/the-omega-institute/trureturing/issues/18607).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Factorial quotient with coefficient 9979200 and shift 3 | `BalaA361035Parity.a` | Literal source expression, using natural-number division. |
| Every natural index, including zero | `BalaA361035Parity.claim` | Universal quantifier over the naturals. |
| Odd exactly when the shifted index is a power of two | `BalaA361035Parity.claim` | Both directions of the iff; the exponent is natural and at least 2. |
| Quotient is an integer | Private `BalaA361034Parity.integrality` | Denominator divides numerator; its hypotheses are discharged in the settling proof. |
| Conjecture holds | `BalaA361035Parity.result` | Complete claim without extra assumptions. |
| Parameters $C,j$ in the shared proof | `BalaA361034Parity.quotient_odd` | Internal generalization, instantiated with $C=9979200$ and $j=3$; no added premise in `result`. |

The dropped or weakened source-clause set is empty.

## Motivation

The settling GID is `D5/S3/Arith/FactorialRatio/BalaA361035Parity.result`.
Its admission basis is `open-problem-resolution (#18607; Proved)`; generality is
`I`, and utility is `none`. The retained declarations are unbounded symbolic
statements, with no retained finite certificate or enumeration.
The companion settlement concerns OEIS A361034 and issue #18606.

## Gap

This is a tier-1 external named conjecture. The preregistration's literature screen
read the OEIS data mirror `oeis/oeisdata` at `e7d0073e` and searched the repository,
`google-deepmind/formal-conjectures`, and the Epoch OEIS benchmark results for the
exact sequence identifiers. No settlement of A361034 or A361035 was found in that
searched scope. Literature completeness is `ASSUMED-UNVERIFIED`.

An external A361033 write-up by Wentao Li at
[commit `0a23974e54b90afd1453ef02c27cf8f617bad940`](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/proofs/new-formalization/A361033/PROOF.md)
asserts integrality and a parity characterization for the adjacent row.
Its Lean source has not been rebuilt under its original toolchain here;
verification of that external artifact is `ASSUMED-UNVERIFIED`.
A361033 is outside the two settling declarations of this delivery.

## Route

The imported `OeisA347854BalaHalfIndexIntegral.mul_div_reduce` reduces floor terms
to quotients and residues, and its `factorial_prod_dvd_of_floor` turns their sum
inequality into factorial divisibility. Cancelling $j!$ gives divisibility by eight
times the numerator. Prime-factorization comparison removes the factor eight:
odd primes do not divide it, and at two the binary digit-sum identity supplies the
needed bound.

For $C>0$, $j>0$, $8j!C=(4j)!$, and $v_2(C)=3j-3$, the private
`integrality` and `quotient_valuation` lemmas give
$$n!(n+j)!^3\mid C(4n)!,\qquad
v_2\left(\frac{C(4n)!}{n!(n+j)!^3}\right)=3\bigl(s_2(n+j)-1\bigr).$$
Here $s_2(m)$ is the sum of the binary digits of $m$.
A positive number has binary digit sum one precisely when it is a power of two;
the shared public `quotient_odd` combines these facts. The settling theorem
instantiates it and derives the source's exponent bound and exact natural subtraction.

## Falsifier

A natural index where the denominator fails to divide the numerator, where the
exact valuation identity fails, or where the stated iff fails would contradict
the corresponding kernel-checked declaration. The source's exponent lower bound
and the zero index remain included.

## Evidence

The Lean source is `D5/S3/Arith/FactorialRatio/BalaA361035Parity.lean`.
Its Blueprint Scribe displays the complete sequence definition, claim, and result.
The compiled private lemmas of `BalaA361034Parity` supply integrality and valuation;
the public `quotient_odd` is consumed by both settling results.

The finite experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/c43d9a8ac71bf4808404401e31f09667ee1f5037/docs/reports/oeis-a361033-a361034-a361035-bala-parity).
At that revision, `python3 check.py 600` exits 0;
`check.py` SHA-256 is `1280afc6923b0c79df6218f8d1a6302064e2542498f2ec64e79f4f32c35b6080`.
For $0\le n\le600$ and $j=1,2,3$, the checker reports integrality, parity iff
$n+j$ is a power of two, the exact valuation $3(s_2(n+j)-1)$, and agreement with
its published-data entries. The final result is `RESULT PASS`.
This finite computation does not establish any uniform extension.

The four-slot escape audit is unfinished for `BalaA361034Parity.quotient_odd`,
`BalaA361034Parity.result`, and `BalaA361035Parity.result`;
[issue #21857](https://github.com/the-omega-institute/trureturing/issues/21857)
records the missing whole-family realization, variation/sensitivity, observational
dependence, and source-selection evidence. No validated registration is claimed.

## Triage

### What the settlement shows

- **Proved (kernel-checked):** the exact parity iff for A361034 and A361035,
  including $n=0$ and the source-specific exponent lower bounds, is stated by
  `BalaA361034Parity.result` and `BalaA361035Parity.result` respectively.
- **Open (external verification):** the adjacent A361033 parity claim is
  asserted by the external write-up cited in Gap. Its Lean artifact is unverified
  here, and no A361033 settling declaration or fidelity check is delivered.
- **Proved (kernel-checked):** the private `BalaA361034Parity.integrality` gives
  denominator divisibility under $C>0$, $j>0$, $8j!C=(4j)!$, and
  $v_2(C)=3j-3$. The two settling proof terms discharge these premises for
  $(C,j)=(2520,2)$ and $(9979200,3)$; these are the two fixed rows certified here. Thus natural-number division agrees
  with the integer quotient.
- **Proved (kernel-checked):** the private `BalaA361034Parity.quotient_valuation`
  gives the exact factorization exponent $3(s_2(n+j)-1)$ under those conditions.
  The private `binary_sum_one` and public `quotient_odd` yield the single nonzero
  binary digit criterion. This is stronger explanatory information than parity alone.
- **Computed:** the pinned experiment in Evidence passes for every tested
  $0\le n\le600$ and $j=1,2,3$, including its published-data comparison, with
  exit 0 and final result `RESULT PASS`.
- **Open:** unconditional all-row A361032 integrality and parity are not
  independently settled here. The shared theorem is a conditional family route;
  the relation $8j!C=(4j)!$ and the valuation hypothesis must both hold.
- **Open:** whether #18606 and #18607 remain unpublished open problems beyond
  the explicitly screened sources is unverified. Broader prior-art clearance
  and literature completeness remain `ASSUMED-UNVERIFIED`.

**Proved in prose:** write $M(n)=(4n)!/(n!^4)$, the multinomial
integer A008977, and $P_j(n)=\prod_{r=1}^{j}(n+r)$. The factorial recurrence gives
$(n+j)!=n!P_j(n)$, so denominator divisibility above implies
$P_j(n)^3\mid C M(n)$ by cancelling the positive factor $n!^4$.
For $(C,j)=(2520,2)$ and $(9979200,3)$ this proves the entry's associated
"appear to have the property" divisibility assertion. This is a consequence of
the displayed identities, not an additional public Lean theorem.
The two settlements remove the parity and integrality assertions for these fixed
rows without supplying a proof for all rows of A361032.

## ASSUMED-UNVERIFIED

Global literature completeness and unpublished-open status beyond the named
search scope are unverified. The finite experiment has only its stated range.
The unfinished escape registration is tracked by #21857; no Reg mirror is delivered.
