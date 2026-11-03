---
slug: a320043-square-values-refutation
bibkey: spezia2018a320043
doi: null
url: https://oeis.org/A320043/internal
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation
---

# A320043: an additional square value

## Problem

Stefano Spezia's sole COMMENTS conjecture in OEIS A320043, revision 43,
says: “Conjecture: a(n) is not a perfect square except for n = 1, 6 and 96.”
The source and its literal first FORMULA are cited in
[the source note](../Library/ArithUnits/spezia2018a320043.md).
For $n\ge1$ the sequence is

$$
 A(n)=\sum_{k=1}^{n}\frac{(n+1-k)^2k}{\gcd(n+1-k,k)^3}.
$$

The assertion is $\forall n\in\mathbb N,\ 1\le n\Rightarrow
\forall m\in\mathbb N,\ A(n)=m^2\Rightarrow(n=1\lor n=6\lor n=96)$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| First FORMULA | `a`, the sum over `Finset.Icc 1 n` with the literal numerator and gcd-cubed denominator | Exact natural quotients on the source domain |
| OFFSET begins at 1 | `1 ≤ n` in `claim` | The empty sum at zero is excluded |
| Perfect square | Natural root `m`, equality `a n = m ^ 2` | All nonnegative square roots |
| Except for 1, 6, 96 | Three alternatives in `claim` | No added exclusion or hypothesis |
| Refutation | `result : ¬ claim` | Unchanged source assertion negated |

For every selected summand, put $u=n+1-k$, $v=k$ and $d=\gcd(u,v)$.
Both $u$ and $v$ are positive. Writing $u=du_0$ and $v=dv_0$ gives
$u^2v/d^3=u_0^2v_0$, so natural division equals the source's exact quotient.
This is a prose derivation of the encoding correspondence.

## Motivation

The external named problem is preregistered in
[#24212](https://github.com/the-omega-institute/trureturing/issues/24212).
The settling node is
`D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.result`.
It refutes the positive-index square exclusion at $n=708158976$ with
$m=144767444036350576$.

## Gap

The source assertion is false. The repository and pinned-Mathlib search
finds no owner of the source sequence or this refutation in the searched
scope. The proof uses existing prime-coprimality, finite-telescope and
Lucas-primality results; its proof shape is bind-only, with admission basis
`open-problem-resolution (#24212; Refuted)`.
Minimality of the extra index and any complete classification remain open.

## Route

The private `prime_row` proves, for every natural prime $p$,
$12A(p-1)=p^2(p^2-1)$. On $1\le k<p$, a common divisor of $p-k$
and $k$ divides $p$ and $k$. Primality of $p$ and $0<k<p$ force
$\gcd(p-k,k)=1$. In integers set

$$
 F(k)=6p^2k(k-1)-4pk(k-1)(2k-1)+3k^2(k-1)^2.
$$

Polynomial expansion gives $F(k+1)-F(k)=12k(p-k)^2$,
$F(1)=0$, and $F(p)=p^2(p^2-1)$. Summation gives the row identity.
The private `prime_pell` proves the conditional consequence
$A(p-1)=(py)^2$ whenever $p^2-12y^2=1$ and $p$ is prime.
The private `witness_prime` certifies $p=708158977$ using `lucas_primality`.
At $y=204427888$, the Pell identity gives the additional square used by `result`.

## Falsifier

An incorrect source domain, nonexact quotient, false Pell identity, or
invalid primality certificate would invalidate the proposed correspondence.
The literal claim retains the source's domain and all three exceptions.
The formal theorem certifies its negation within Lean's permitted axiom closure.

## Evidence

The Lean owner is
[D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.lean](../D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.lean),
with its [Blueprint](../Blueprint/D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.md).
The only public theorem is `D5.S3.ArithSums.SpeziaA320043SquareValuesRefutation.result`.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Exact experiment

[Experiment directory at immutable revision b611c1901c5ef2abe181c55fb1daaf62484adbf8](https://github.com/the-omega-institute/trureturing-experiments/tree/b611c1901c5ef2abe181c55fb1daaf62484adbf8/docs/reports/spezia-a320043).
The script is `docs/reports/spezia-a320043/check.py`; SHA-256:
`575d499704473bb4eb6eaed37a87e622b30f331a075641801edff85861282c1b`.
The immutable script was extracted with `git show` and executed with
`python3 /Users/auric/.sshx/2e1b726df82d42d90bc35ace/attempt-1/check.py`, exit 0.
All 42 source DATA terms agree with the literal sum. Integer and independent
rational evaluations agree for every $1\le n\le256$; precisely $1,6,96$
are square indices in that range, and $A(96)=7376656=2716^2$.
The script checks the row identity directly at every prime $p\le257$
(55 primes), the telescope symbolically, and the Pell doubling identities.
It checks the witness factorization, modular certificate and primality by
trial division through $26611$. It deduces the large row algebraically;
it does not enumerate that row or test all preceding indices.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and scope |
| --- | --- | --- |
| Prime gcd reduction, telescope and square mechanism | Proved in prose; derivation in Route | A common divisor of $p-k$ and $k$ divides $p$ and the positive $k<p$, hence equals one. The displayed polynomial difference and endpoints telescope to the row identity; substitution of the Pell equation gives the square. |
| Conditional prime/Pell mechanism for every natural prime and root | Proved; kernel-checked private `prime_pell` | For all natural $p,y$, primality and $p^2-12y^2=1$ imply $A(p-1)=(py)^2$. |
| Extra index positive and distinct from all source exceptions | Proved; kernel-checked `result` | $n=708158976$, $m=144767444036350576$ contradict the unchanged claim. |
| Square indices on $1\le n\le256$ and value at 96 | Computed; exact experiment above, exit 0, pinned script and SHA-256 | Exactly $1,6,96$; $A(96)=7376656=2716^2$. |
| Pell doubling and the composite intermediate | Computed; exact experiment above, exit 0, pinned script and SHA-256 | $(7,2)\mapsto(97,28)\mapsto(18817,5432)\mapsto(708158977,204427888)$, with $18817=31\cdot607$. No prime-row formula at composite inputs is asserted. |
| Smallest additional square index | Open | No exhaustive exclusion of $257\le n<708158976$ is established. |
| Infinitely many prime/Pell inputs | Open | The finite chain and one certified prime do not establish infinitude. |
| Other square mechanisms and all square indices | Open | No classification is established. |

Primality is a sufficient condition for eliminating the gcd denominators;
the Pell equation is a sufficient condition for the resulting row to be a
square. These are not asserted to be necessary conditions. The restricted
observation on $1\le n\le256$ survives, as do the three source examples.
The inspected source's other displayed formulas do not depend on the
conjecture; the refutation supplies no revision of those formulas
(evidence kind: source reading in #24212).

## ASSUMED-UNVERIFIED

Literature completeness and priority remain `ASSUMED-UNVERIFIED`.
The screen in #24212 inspected OEIS revision 43, arXiv metadata/full-text
queries, public code and formalization corpora, and available catalogue
results without locating a settlement. OpenAlex, Semantic Scholar,
MathOverflow, broad web searches and MathDB had access or rate-limit
boundaries. Full texts of Lloyd (1997), DOI 10.2307/3619201, and Delany,
Douglass, Breen and Eggleton (1990), DOI 10.2307/2324410, were not available;
metadata and previews alone do not exclude indirect prior art.
Minimality, infinitude and classification retain their open status.
