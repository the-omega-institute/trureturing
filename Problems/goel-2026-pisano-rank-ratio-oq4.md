---
slug: goel-2026-pisano-rank-ratio-oq4
bibkey: goel2026sophiegermain
doi: null
url: https://arxiv.org/abs/2604.17847v3
triage: theorem
motivation_gids:
  - D5/S3/Arith/GoelPisanoRatioRefutation.result
---

# Goel's OQ4: Fibonacci period-to-rank ratios omit five

## Problem

Aradhya Goel, *Sophie Germain Primes and the Totient of Fibonacci Numbers*,
arXiv:2604.17847v3, Section 10, OQ4, p. 10, asks:

> **OQ4. Values of $\pi(q)/z(2q+1)$.** Is $\{\pi(q)/z(2q+1):q>5\text{ with }z(2q+1)\mid\pi(q)\}=\{\text{odd integers}\}$?

The versioned TeX source reads verbatim:

```tex
\item[OQ4.] \textbf{Values of $\pi(q)/z(2q+1)$.} Is $\{\pi(q)/z(2q+1) : q > 5 \text{ with } z(2q+1) \mid \pi(q)\} = \{\text{odd integers}\}$?
```

The Introduction defines $z(p)$ at primes as the least positive index $k$ with
$p\mid F_k$, and $\pi(n)$ as the period of the Fibonacci residues modulo $n$.
The standing domain in Sections 5–7 is Sophie Germain primes: $q$ and $2q+1$
are both prime. The assertion here uses $q>5$ and $z(2q+1)\mid\pi(q)$.
The right-hand side is the positive odd integers; reading it as all odd integers
also fails because the ratios are positive.

## Motivation

The frozen declaration `D5/S3/Arith/GoelPisanoRatioRefutation.result` has type
`¬ claim`, where `claim` is the displayed equality of natural-number sets with
the complete standing prime domain. The resolution kind is Refuted.

## Gap

Preregistration [#13841](https://github.com/the-omega-institute/trureturing/issues/13841)
identifies this as a Tier 1 numbered external question. Its literature screen
checked the versioned source, MathDB queries “Pisano period rank apparition”,
“Sophie Germain totient Fibonacci” and “Goel Fibonacci”, and repository owners.
No resolution of OQ4 was found in that searched scope. This is a bounded
negative search result, not a claim of exhaustive worldwide priority.

## Route

Put $p=2q+1$ and $\varepsilon(r)=(5/r)$, the Legendre symbol at a prime.
The frozen rank and apparition theorems give
$z(p)\mid p-\varepsilon(p)$ and the usual return-pair bounds on $\pi(q)$.
If $\varepsilon(p)=1$, then $z(p)$ divides both $2q$ and $q^2-1$, hence $2$.
If $\varepsilon(q)=1$ after $\varepsilon(p)=-1$, then $z(p)$ divides both
$q-1$ and $2(q+1)$, hence $4$. Both contradict $z(p)\ge5$ for $p>11$.
Thus $\varepsilon(q)=-1$, so $q\equiv2$ or $3\pmod5$ and
$\pi(q)\mid2(q+1)$. Consequently $5\nmid\pi(q)$ and
$5\nmid\pi(q)/z(p)$. The odd number $5$ cannot belong to the value set.

## Falsifier

A Sophie Germain prime $q>5$ satisfying $z(2q+1)\mid\pi(q)$ and
$5\mid\pi(q)/z(2q+1)$ would contradict the exclusion on the proof path.
A finite search with no such value does not establish this universal exclusion;
the kernel-checked `result` establishes the negation of OQ4.

## Evidence

The formal definitions use `Nat.fib`, natural-number divisibility, and the
least-positive-period infimum
$\operatorname{sInf}\{k\in\mathbb N:0<k\land\forall m\in\mathbb N,
F_{m+k}\bmod n=F_m\bmod n\}$.
The rank is the existing `FibonacciAtomic.TimeSampling.zeroRank` with its literal
least-positive-zero expression. `result` has no hypotheses. Its axiom closure is
contained in `{propext, Classical.choice, Quot.sound}`.
The source's Lemma 6.3 and Theorem 7.1 also imply the exclusion on paper; the
formal proof uses existing frozen Fibonacci declarations and consumed private
bridges for the literal period definition.

## Triage

Tier 1; `admission_basis: open-problem-resolution` with preregistration #13841;
`proof_shape: bind-only`; `escape_witness: none`. The only public theorem is
`result`. All private auxiliaries are consumed on its proof path. The symbolic
argument has `utility: none`. Information-escape registration is paused under
CLAUDE.md §3.9.

### What the settlement shows

- **Proved in this module:** OQ4 is false (`D5/S3/Arith/GoelPisanoRatioRefutation.result`).
  The consumed private steps `epsilon_q_negative`, `five_not_dvd_pi` and
  `ratio_avoids_five` establish the failure mechanism uniformly in every eligible
  prime: the negative quadratic character forces a period bound coprime to $5$.
  In particular, no odd multiple of $5$ is attained. These private steps are
  proof components, not additional public settlement declarations.
- **Open:** whether the value set is exactly the positive odd integers coprime
  to $5$. **Computed:** for $7\le q<200000$, among 2055 Sophie Germain primes,
  489 satisfy the divisibility condition; all 489 ratios are odd and coprime
  to $5$, and all corresponding primes satisfy $q\equiv8\pmod{15}$.
  The observed values and multiplicities are `[[1, 317], [3, 128], [7, 3], [9, 19], [11, 4], [13, 1], [17, 2], [21, 3], [27, 1], [33, 2], [39, 1], [43, 1], [63, 1], [69, 2], [81, 1], [97, 1], [357, 1], [1377, 1]]`.
  First occurrences in the same window (the smallest eligible $q$ for each ratio) are:

  | ratio | first $q$ |
  | --- | --- |
  | 1 | 83 |
  | 3 | 23 |
  | 7 | 16673 |
  | 9 | 20393 |
  | 11 | 75503 |
  | 13 | 95393 |
  | 17 | 117503 |
  | 21 | 40823 |
  | 27 | 85103 |
  | 33 | 1583 |
  | 39 | 161303 |
  | 43 | 16253 |
  | 63 | 97523 |
  | 69 | 65963 |
  | 81 | 59453 |
  | 97 | 91373 |
  | 357 | 147083 |
  | 1377 | 126683 |

  In that window $19$ and $23$ do not occur. No claim of global nonattainment
  follows from this bounded absence. For $q=23$, $\pi(23)=48$ and $z(47)=16$,
  giving ratio $3$.
- **Computed:** extending the least-positive-zero definition to composite
  arguments changes the question. At $q=241$, $2q+1=483$ is composite,
  $\pi(q)=240$, $z(483)=24$, and the ratio is the even number $10$.
  At $q=30661$, $2q+1=61323$ is composite, $\pi(q)=10220$,
  $z(61323)=2044$, and the ratio is $5$.
  Each period and rank is also checked by direct recurrence iteration.
  These are examples for the extended domain; they do not contradict the
  prime-domain exclusion. **Open:** classification of the extended-domain values.
- **Computed:** the quotient lower bound in the source's Theorem 6.2 is odd
  for every eligible prime in the stated window. The value of $|S(q)|$ itself
  is not computed here. **Proved on this module's proof path:** the lower bound
  $\pi(q)/z(2q+1)$ is also coprime to $5$. This does not imply that $|S(q)|$
  is coprime to $5$: being a lower bound supplies no divisibility relation.
  **Open:** a Lean formalization of the full $S(q)$ counting statement and any
  further restriction on $|S(q)|$. The source's Theorems 6.2 and 7.1 require
  no equality with all odd integers, so the refutation supplies no refutation
  of those theorems. OQ4 is the closing question being settled.

### Reproducible computations

All items marked computed above use the following self-contained script,
with Python 3 and SymPy 1.14.0. Save the block as `/tmp/goel-oq4-triage.py`.
Command: `python3 /tmp/goel-oq4-triage.py`. Exit code: `0`.
SHA256 of the exact UTF-8 script, including its final newline: `ad9c92e63ba8647cbdb7efc9fef0716ad4bf2af35ddba6d291a77afd48dc6dd5`.
The prime-period divisor search uses the classical bound $\pi(p)\mid p^2-1$
for $p\ne5$, and $\pi(5)=20$. The composite rank search uses the least common
multiple of the prime-power period bounds. Direct iteration independently
checks the two extended-domain examples and the $q=23$ example.

```python
import json
from collections import Counter
from math import lcm
from sympy import divisors, factorint, isprime, primerange

def fibpair(n, modulus):
    if n == 0:
        return 0, 1 % modulus
    a, b = fibpair(n // 2, modulus)
    c = a * (2 * b - a) % modulus
    d = (a * a + b * b) % modulus
    return (d, (c + d) % modulus) if n % 2 else (c, d)

def prime_period(p):
    bound = 20 if p == 5 else p * p - 1
    return next(k for k in divisors(bound) if fibpair(k, p) == (0, 1 % p))

def rank(n):
    bound = 1
    for p, e in factorint(n).items():
        bound = lcm(bound, prime_period(p) * p ** (e - 1))
    return next(k for k in divisors(bound) if fibpair(k, n)[0] == 0)

def direct(n):
    a, b, k, first_zero = 0, 1, 0, None
    while True:
        a, b = b, (a + b) % n
        k += 1
        if a == 0 and first_zero is None:
            first_zero = k
        if (a, b) == (0, 1):
            return k, first_zero

bound = 200000
eligible, total = [], 0
for q in primerange(7, bound):
    if not isprime(2 * q + 1):
        continue
    total += 1
    period, z = prime_period(q), rank(2 * q + 1)
    if period % z == 0:
        eligible.append((int(q), int(period), int(z), int(period // z)))
assert len(eligible) == 489
assert all(q % 15 == 8 and r % 2 == 1 and r % 5 != 0 for q, _, _, r in eligible)
counts = Counter(r for _, _, _, r in eligible)
first_q = {}
for q, _, _, r in eligible:
    first_q.setdefault(r, q)
composite_examples = []
for q in [241, 30661]:
    n = 2 * q + 1
    period, z = prime_period(q), rank(n)
    assert isprime(q) and not isprime(n)
    assert direct(q)[0] == period and direct(n)[1] == z
    assert period % z == 0
    composite_examples.append(dict(q=q, n=n, period=int(period), rank=int(z), ratio=int(period // z)))
assert composite_examples[0]['ratio'] == 10
assert composite_examples[1]['ratio'] == 5
assert direct(23)[0] == 48 and direct(47)[1] == 16
print(json.dumps(dict(bound_exclusive=bound, sophie_germain_count=total,
    eligible_count=len(eligible), ratio_counts=sorted(counts.items()), first_q=first_q,
    residues_mod15=sorted(set(q % 15 for q, _, _, _ in eligible)),
    missing_odd_coprime5_through199=[r for r in range(1, 200, 2) if r % 5 and r not in counts],
    q23=dict(period=48, rank47=16, ratio=3), composite_examples=composite_examples,
    sympy_version=__import__('sympy').__version__), sort_keys=True))
```

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources and queries recorded above.
The computation is finite experimental evidence, not a Lean certificate for
its table or for global attainment. The corrected and composite-domain
classification questions remain open. No new axiom or assumption is used by
the settling Lean declaration.
