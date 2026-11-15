---
slug: oeis-a085124-murthy-joint-digit-product
bibkey: murthy2003a085124
doi: null
url: https://oeis.org/A085124
triage: theorem
motivation_gids:
  - D5/S1/Digit/MurthyA085124.result
---

# Murthy's joint decimal digit-product conjecture

## Problem

Amarnath Murthy's OEIS A085124 (2003), revision 23, has the NAME:

> Smallest multiple of n whose digital product is also a positive multiple of n, or 0 if no such number exists.

Its COMMENTS state, verbatim:

> a(n) = 0 if n is not a term of A002473 (i.e., not a 7-smooth number).
>
> a(n) = 0 if n is a multiple of 10.
>
> Conjecture: otherwise, a(n) is positive.

Let $P(N)$ be the product of the ordinary decimal digits of $N$, with no
leading zeros. For every integer $n\geq1$, the complete target is

$$
\bigl(\exists N>0:\ n\mid N,\quad P(N)>0,\quad n\mid P(N)\bigr)
\quad\Longleftrightarrow\quad
\bigl(\forall p\text{ prime},\ p\mid n\Rightarrow p\leq7\bigr)
\ \land\ 10\nmid n.
$$

The source sequence is the least such positive $N$, or zero if the set is
empty. The target includes its exact identification with `a085124`, positivity
classification, zero branch, qualification and leastness among all qualifying
$N$. There is no bound on $n$, $N$, digit length or prime exponents; $n=1$
is included. Both divisibilities have $n$ on the left.

## Motivation

The conjecture asks whether the two elementary obstructions are complete.
A zero-free multiple alone does not control the product of its digits.
The joint condition requires one decimal word to satisfy both divisibilities.
The registered whole question is issue
[30909](https://github.com/the-omega-institute/trureturing/issues/30909).

## Gap

The source states the obstructions and conjectures their sufficiency.
`D5/S1/Digit/MurthyA085124.result` proves that sufficiency together with
necessity and the full least-positive-or-zero bridge. The proof connects
constructed words to canonical decimal expansions, rather than merely
producing a formal list with the desired product.

## Route

Write $n=p^k m$, where $p$ is two or five,
$\gcd(m,10)=\gcd(p^k,m)=1$. The assumption $10\nmid n$ permits this
decomposition, including $k=0$. N. S.'s zero-free suffix construction lifts
one digit at a time to obtain a length-$k$ suffix $S$ whose value is divisible
by $p^k$; $S$ is empty when $k=0$.

In least-significant-first order, set
$W=S\mathbin{++}(1::\operatorname{primeFactorsList}(n))$, retaining prime
multiplicity. All its digits lie between one and nine, the block is nonempty,
its value is divisible by $p^k$, and its digit product is divisible by $n$.
Put $b=10^{|W|}$ and $t=\varphi(m(b-1))>0$. Euler's theorem modulo
$m(b-1)$ and the geometric-sum identity give
$m\mid\sum_{i<t}b^i$ after cancellation of $b-1$. Repeating $W$ exactly
$t$ times therefore gives a positive multiple of $n$ whose positive digit
product, $P(W)^t$, is also divisible by $n$.

Conversely, a prime divisor of $n$ divides some nonzero decimal digit of a
qualifying $N$, hence is at most seven. A multiple of ten has a terminal
zero and cannot qualify. `Nat.digits`/`Nat.ofDigits` reconstruction excludes
leading zeros. `Nat.find_spec` and `Nat.find_min'` identify the least
qualifying number, with zero exactly when no witness exists.

The suffix lifting and block repetition are prior mathematics from N. S.'s
[answer](https://math.stackexchange.com/a/2067782) and
[lifting comment](https://math.stackexchange.com/questions/2067752#comment4448589_2067782).
The prime-factor word that imposes joint divisibility is a repository-derived
application. No upstream Lean source is copied; the Library notes are
citation-only and do not claim a license to reproduce upstream text or code.

## Falsifier

A positive $n$ satisfying the prime-factor and nondivisibility conditions
with no qualifying $N$, or a qualifying $N$ for an $n$ violating either
condition, would refute the classification. A positive `a085124 n` that
fails to qualify, a smaller qualifying $N$, or a zero value with an existing
witness would refute the corresponding sequence bridge.

## Evidence

The exact result is `D5/S1/Digit/MurthyA085124.result`. For every positive
natural $n$, its four conjuncts establish:

- Existence of an `admissible n N` exactly under the source conditions.
- Positivity of `a085124 n` exactly under those same conditions.
- `a085124 n = 0` exactly when no admissible $N$ exists.
- Whenever positive, `a085124 n` is admissible and is at most every
  admissible $N$.

`admissible n N` means $0<N$, $n\mid N$, $0<P(N)$ and $n\mid P(N)$.
The proof uses the existing `DigitProductSlices.digitProduct` definition;
it does not use an opposite-divisibility classification. The Reg mirror
retains the whole positive-$n$ telescope and all four clauses, using the
actual sequence as a dependent-family readout. Its nonconstant behavior
is witnessed by positivity at one and the zero value at ten.

## Triage

`theorem`. The classification and exact least-or-zero bridge are proved by
`D5/S1/Digit/MurthyA085124.result` for all positive inputs.

### What the settlement shows

The two source obstructions are jointly sufficient, with no restriction on
prime exponents or decimal length. The construction controls the value and
digit product of the same word; arbitrary zero-free multiples alone supply
only part of that conclusion. Thus all three quoted source comments are
accounted for, including the conjectured positive branch. This does not
establish any unquoted claim about other OEIS entries.

The stronger statement that a qualifying number can contain any prescribed
finite zero-free word as a contiguous digit block remains open here. It is
a separate candidate, not an additional conclusion of the settling theorem.
No efficient formula or upper bound for the least witness is asserted.

## ASSUMED-UNVERIFIED

Worldwide or first-publication priority is not established. The bounded
source and literature screen found no exact resolution; it does not exclude
private, unindexed or unexamined proofs. He and Sanna's
arXiv:2403.14812v2 concerns the opposite divisibility $P(N)\mid N$.

The bounded Lean search covered repository declarations including private
ones, pinned Mathlib digit/list/number-theory results, and the reported
third-party screen. The reported authenticated GitHub A085124/digit-product
searches had zero exact hits; the inspected tinycryptids/compfiles/atlas
candidates concern different claims. This does not claim exhaustive body
coverage or admissibility of a third-party library. A supplementary
literature-only CLI call timed out without a valid result and adds no
completed search or negative-resolution evidence.

The identification with the OEIS entry is documentary. The Lean kernel
checks the explicitly defined decimal predicate and sequence; it does not
establish an external entry's current editorial or worldwide open status.
