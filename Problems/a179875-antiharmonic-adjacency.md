---
slug: a179875-antiharmonic-adjacency
bibkey: eldar2021a179875
doi: null
url: https://oeis.org/A179875
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/EldarAntiharmonicAdjacency
---

# Eldar's antiharmonic adjacency conjecture

## Problem

Amiram Eldar's OEIS A179875 COMMENT, revision 13, states:

> Conjecture: also numbers k such that mu(k) = 1 and mu(k+1) = -1, where mu is the Möbius function (tested on the first 10^4 terms).

The NAME is:

> Numbers h such that h and h+1 have same antiharmonic mean of the numbers k < h such that gcd(k, h) = 1.

The ratio is $B(n)=S_2(n)/S_1(n)$, where
$S_j(n)=\sum_{1\le k\le n,\ \gcd(k,n)=1} k^j$.
The binding positive-inclusive convention gives $S_j(1)=1$; for $n>1$
coprimality excludes the upper endpoint. Both moments are natural sums,
cast to the rationals before division. The term $k=1$ makes the denominator
positive for every positive modulus.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Positive indices h or k | Natural n with hypothesis $1\le n$ in claim | No additional arithmetic restriction |
| A053818 sum of squared totatives | totativeMoment at exponent 2 | Literal inclusive coprime sum |
| A023896 positive reduced residues; a(1)=1 | totativeMoment at exponent 1 | Literal inclusive convention |
| A053818(n)/A023896(n) | antiharmonicMean | Rational quotient |
| h and h+1 have the same mean | Equality in claim | Full rational values |
| also numbers with mu(k)=1, mu(k+1)=-1 | Biconditional in claim | Both implications, integer-valued Möbius function |

The exponent parameter $j$ merely shares the two literal sum definitions.
The result has no additional binder or hypothesis. Equality of reduced
numerators alone or denominators alone is outside the assertion.

## Motivation

The moment identities convert equality of two finite rational sums into
an extremal condition on prime support. The settling declaration is
`D5/S3/ArithSums/EldarAntiharmonicAdjacency.result`.
The module has generality G and utility none. Its admission basis is
open-problem-resolution (#24175; Proved).

## Gap

[Preregistration #24175](https://github.com/the-omega-institute/trureturing/issues/24175)
identifies an external Tier 1 conjecture. The bounded source screen reads
OEIS revision 13 and Petridi, arXiv:1612.07632v2. Petridi's Section 1 records
the classical first and second moments, with the second attributed there
to Pólya–Szegő; it does not state Eldar's adjacency classification.
A175505 already records Hasler's normalized mean formula. The settlement
uses those classical ingredients and makes no originality claim for them.

The screened OpenAlex identifier lookup and Crossref title search did not
identify a journal version. OpenAlex citation enumeration and title
search were rate limited. The inspected GitHub/LODA sequence material
supplied no settlement proof. Search completeness is ASSUMED-UNVERIFIED;
absence in the inspected scope does not prove absence worldwide.

## Route

The private sum_multiples proof constructs the bijection $k\mapsto dk$,
with inverse natural division. The private moment_moebius proof uses it
with Möbius cancellation to express each literal moment as a divisor sum.
The first_power_sum and second_power_sum proofs apply the imported public
owners `ConjectureMachines.Semantics.Riemann.VonMangoldtCount.sum_Icc_two_mul_pow_one`
and `ConjectureMachines.Semantics.Riemann.VonMangoldtCount.sum_Icc_six_mul_pow_two`
from `D5/S3/Weil/Mertens/Cryptids/VonMangoldtCount/Foundation`, after an
injective rational-to-real cast. There is no publication or re-pin of that owner.

Let $r(n)=\operatorname{rad}(n)$ and
$e(n)=(-1)^{\omega(n)}r(n)/n$ for positive $n$.
The private normalized_moment proof gives $3B(n)=2n+e(n)$, including $n=1$
by direct evaluation. The private error_bounds and error_endpoint proofs
give $|e(n)|\le1$ and $e(n)=s\iff\mu(n)=s$ for $s\in\{1,-1\}$.
The public result combines these facts to prove the complete claim.

## Falsifier

A positive index for which either direction of the literal rational
biconditional fails would refute the claim. Replacing rational equality
with equality of reduced numerators is invalid: $B(3)=5/3$ and $B(4)=5/2$
have equal numerators and unequal means. No finite computation establishes
the universal result.

## Evidence

The module `D5/S3/ArithSums/EldarAntiharmonicAdjacency` contains the
kernel-checked theorem result of type claim. Its public surface consists
of totativeMoment, antiharmonicMean, claim and result. All proof helpers
are private and consumed. The axiom closure of every public declaration
is contained in {propext, Classical.choice, Quot.sound}.
The Blueprint mirror displays all definition bodies and the expanded result.

The escape audit for `D5.S3.ArithSums.EldarAntiharmonicAdjacency.result`
is unfinished under [#25446](https://github.com/the-omega-institute/trureturing/issues/25446).
No successful Reg source or declared_validated registration is claimed.
The finite primitive iff arena does not preserve the universal positive
natural domain; a source-bound dependent-family reconstruction, variation,
sensitivity and observational-dependence evidence are missing.

### Exact finite experiment

The experiment is in
[trureturing-experiments at 803b763910fb729ab57e42e9c84e778771e29abc](https://github.com/the-omega-institute/trureturing-experiments/tree/803b763910fb729ab57e42e9c84e778771e29abc/docs/reports/eldar-a179875).
Program: `docs/reports/eldar-a179875/check.py`.
SHA-256: `337ca75678c45d77b04821820aff8ddf6e0eac5854f0e265eb105f73f75923bd`.
The implementation seat ran the identical pinned bytes with
`python3 /Users/auric/.sshx/a701d4808fb24940451f7fdb/attempt-1/checks/experiment-check.py`,
exit 0. It reproduced all 43 displayed terms through 502; verified the
classical moments for $2\le n\le2000$, normalized moments and endpoint
tests for 2,000 positive indices, and adjacency and monotonicity for
1,999 pairs; 161 pairs had equal means. The final marker is ALL_CHECKS_OK.
This is finite computational evidence, not the universal proof.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Mechanism | Proved; kernel-checked private normalized_moment, error_bounds, error_endpoint and public result | For every positive n, $3B(n)=2n+e(n)$ and $|e(n)|\le1$. Adjacent equality forces $e(n)=1$, $e(n+1)=-1$, equivalent to Möbius signs $(1,-1)$. |
| Endpoint | Proved in prose by direct evaluation | $S_1(1)=S_2(1)=S_1(2)=S_2(2)=1$, so $B(1)=B(2)=1$. The universal result includes this index. |
| Monotonicity | Proved in prose from the kernel-checked normalized_moment and error_bounds identities | For $n\ge1$, $3(B(n+1)-B(n))=2+e(n+1)-e(n)\ge0$, hence $B(n)\le B(n+1)$. This is not an additional delivered Lean theorem. |
| Strict separation | Proved in prose from the same identities | For $n\ge1$, $m\ge n+2$, $3(B(m)-B(n))=2(m-n)+e(m)-e(n)\ge2>0$. Thus $B(n)<B(m)$ and three consecutive means cannot all agree. This is not an additional delivered Lean theorem. |
| Finite source check | Computed; exact finite experiment above | All 43 displayed entries through 502 reproduced; 161 equal pairs among 1,999 adjacent pairs; exit 0 and ALL_CHECKS_OK. No uniform assertion follows from this test alone. |
| Surviving neighbours | Open | Infinitude of equal pairs, A179873's integral-mean conjecture and higher-moment classifications are not settled. |

The endpoint bound is sharp: $e(1)=1$ and $e(2)=-1$. Equality is exactly
simultaneous saturation of opposite endpoints; no squarefree assumption
is imposed on the original domain. The arithmetic classification settles
the full positive-index adjacency question. Petridi's other results and
higher-power questions are not altered, and no source result depending
on Eldar's conjecture is identified in the inspected sources.

## ASSUMED-UNVERIFIED

Literature completeness and global priority remain unverified. The finite
experiment has precisely the tested scope stated above. The four-slot
escape registration remains unfinished under #25446. Neither that issue
nor a CI check is a substitute for the kernel proof or audit evidence.
