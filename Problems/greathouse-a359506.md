---
slug: greathouse-a359506
bibkey: greathouse2023a359506
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Arith/Additive/GreathouseA359506XorBound.result
url: https://oeis.org/A359506/internal
---

## Problem

Charles R. Greathouse IV's FORMULA conjecture in OEIS A359506, revision 41, states: “Conjecture: a(n) <= 5(n+1)/3.” Peter Kagey's entry defines $a(n)$ as the least endpoint $m$ of a finite strictly increasing sequence of nonnegative integers beginning at $n$, ending at $m$, and having bitwise XOR zero. The preregistration is [#23097](https://github.com/the-omega-institute/trureturing/issues/23097). The source note is [greathouse2023a359506](../Library/ArithUnits/greathouse2023a359506.md).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Nonnegative integer entries and every starting value | Natural-number lists and universal $n\in\mathbb N$, including zero | Exact carrier |
| Finite strictly increasing sequence | `HasZeroXorSequence`: a list with `List.Pairwise` strict order | Every earlier entry is smaller |
| First entry $n$ and last entry $m$ | Nonempty list, `List.headD` and `List.getLastD`, both with default zero | On nonempty lists these are the endpoints, as in the binding convention on #23097 |
| XOR of all entries is zero | Literal `List.foldr` of natural bitwise XOR with initial zero | The public sequence predicate retains the source convention; proofs use the published `EllisThanatipanondaCutFamilyA.xs` through `sequence_iff` |
| Least endpoint | `IsLeastEnder`: existence of $m$ and universal comparison with every other eligible $m'$ | Global minimum, without a search cutoff |
| $a(n)\le 5(n+1)/3$ | $3m\le5(n+1)$ | Equivalent rational inequality with positive denominator three |
| Implicit existence of the sequence minimum | Explicit existential $m$ in `claim` | Makes the source's defined minimum meaningful; no weakening |

## Motivation

The bound controls the endpoint of every minimal increasing zero-XOR sequence. The exact endpoint is determined by the power of two dividing $n+1$ and its odd cofactor. The constant $5/3$ is attained on an infinite family.

## Gap

The inspected OEIS revision labels the bound as a conjecture. Kagey's linked note proves the bijection/inverse property, rather than this quantitative bound. The source and literature screen is recorded in #23097. No located work in that screen settles the bound; literature completeness is `ASSUMED-UNVERIFIED`.

## Route

For $n>0$, write $n+1=2^s(2k+1)$. When $k\ge1$, put $q=2^s$. The four terms $q(2k)+(q-1)$, $q(2k+1)+(q-1)$, $q(2k+2)$ and $q(2k+3)$ form an increasing zero-XOR sequence. Their low blocks cancel, and the adjacent even/odd quotient pairs each have XOR one.

If an eligible endpoint were below $q(2k+3)$, every later entry would have quotient $2k+1$ or $2k+2$ after division by $q$. The XOR of a list supported on two values lies in $\{0,a,b,a\mathbin{\mathrm{XOR}}b\}$. Projecting the zero-XOR equality to the high blocks would put $2k$ in that set, contrary to positivity, distinctness and parity. Thus the displayed endpoint is least.

For $n=2^{s+1}-1$, the triple $2^s+(2^s-1)$, $2\cdot2^s+(2^s-1)$, $3\cdot2^s$ has XOR zero. Below its endpoint every later entry has quotient two after division by $2^s$, whereas the starting quotient is one. The same fold invariant excludes a smaller endpoint. The singleton list $[0]$ handles $n=0$.

The module uses `Nat.exists_eq_two_pow_mul_odd` for the factorization, `List.foldr_map_hom` and `Nat.xor_div_two_pow` for quotient projection, and `Nat.testBit_two_pow_mul_add` for binary blocks. These are Mathlib dependencies on the elaborated proof path. The D5 import supplies the published `EllisThanatipanondaCutFamilyA.xs`; `sequence_iff` connects it to the literal fold in the public predicate.

## Falsifier

A natural starting value with no least zero-XOR endpoint, or a least endpoint violating $3m\le5(n+1)$, contradicts `result`. Finite testing does not establish the universal statement. Its proof includes both an explicit eligible endpoint and a lower bound against every eligible endpoint.

## Evidence

The frozen settling declaration is `D5.S3.Arith.Additive.GreathouseA359506XorBound.result`, proving `claim`. The public definitions retain the source's sequence and minimum conditions. The private exact-minimum theorems are consumed by the settling proof. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

Four-slot escape registration for `result` is unfinished: [#25579](https://github.com/the-omega-institute/trureturing/issues/25579). A lawful dependent-family registration still needs exact source reconstruction, its equivalence bridge, whole-family variation/sensitivity and observational-dependence evidence. No Reg mirror or validated registration is claimed.

### Experiment

The independent integer checker is in [trureturing-experiments, pinned directory](https://github.com/the-omega-institute/trureturing-experiments/tree/d94908eea9683284b6755fa762e2d2b3a2a9e450/docs/reports/greathouse-a359506-xor-bound). The checked script is `check.py` at that revision; `git cat-file -e` verified the immutable object. The script is run with `python3 /tmp/op-greathouse359506t/takeover/check.py`, exit 0. Its SHA-256 is `cb0fbf202b9124fa9dbd6d35fa82b84a30d60466eeebbed2baff96e6689cb56c`. It reproduces $a(0),\ldots,a(10)=[0,3,5,6,7,10,9,12,11,14,13]$, checks exact minima and the bound for $0\le n\le512$, and checks the sharp family for $0\le s\le12$; its final check is `ALL_CHECKS_OK`.

## Triage

| Target item | Status and evidence |
| --- | --- |
| Binding bound, existence and global minimality for every $n$ | **Proved, kernel-checked:** `GreathouseA359506XorBound.result` |
| For every $s,k$ with $k\ge1$, the least endpoint of $2^s(2k+1)-1$ is $2^s(2k+3)$ | **Proved, kernel-checked:** private `regular_least` |
| For every $s$, the least endpoint of $2^{s+1}-1$ is $3\cdot2^s$ | **Proved, kernel-checked:** private `power_least` |
| The factor $5/3$ is attained at every $n=3\cdot2^s-1$, with least endpoint $5\cdot2^s$, and cannot be decreased | **Proved in prose:** the derivation below specializes the kernel-checked `regular_least`; no separate public sharpness theorem is claimed |
| Published prefix, exact minima and bound on $n=0,\ldots,512$, sharp family on $s=0,\ldots,12$ | **Computed:** the pinned experiment above, exit 0 and the stated script SHA-256; no larger computational scope is claimed |
| Separate A359507 span and A359508 recurrence/valuation settlements | **Open:** neither independent named settlement is delivered; the exact-minimum families provide a route |

### What the settlement shows

The decisive mechanism is projection to high binary blocks and closure of a two-valued list's XOR in a four-element set. It supplies exact minima for every positive starting value, split into the two kernel-checked families above. In prose, $a(0)=0$: the singleton list $[0]$ is eligible, and every natural endpoint is at least zero. These statements impose no bound on list length or on the starting value.

For sharpness, substitute $k=1$ into `regular_least`. Since $2\cdot1+1=3$ and $2\cdot1+3=5$, the least endpoint for $n=3\cdot2^s-1$ is $m=5\cdot2^s$. Positivity of $2^s$ gives $n+1=3\cdot2^s$ and $3m=5(n+1)$. Therefore every real coefficient $c<5/3$ fails on this family: $m/(n+1)=5/3$. Distinct powers of two give infinitely many distinct starting values. This is a prose consequence of the exact-minimum theorem, rather than an additional kernel-checked declaration.

The exact formulas determine the endpoint increment $m-n$: it is $2^{s+1}+1$ in the regular family and $2^s+1$ in the power family. These are algebraic consequences proved in prose by subtracting the displayed endpoints. Identifying them with the source definitions of A359507, or deriving the A359508 recurrence and valuation formulas with their exact indexing conventions, remains open in this delivery. No dependent result of Kagey's note needs this bound: the inspected note proves its bijection/inverse statement independently.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The preregistration's discovery screen includes rate-limited arXiv, OpenAlex and Semantic Scholar endpoints; no exhaustive citation-absence or priority claim follows. The external open status is limited to the inspected source and searches. Four-slot escape registration remains unfinished under #25579. Finite experimental evidence does not replace the universal Lean proof or settle either neighbouring conjecture.
