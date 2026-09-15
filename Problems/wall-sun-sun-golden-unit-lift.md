---
slug: wall-sun-sun-golden-unit-lift
bibkey: shi2026second
doi: 10.48550/arXiv.2603.25343
triage: wall
motivation_gids:
  - D5/S0/Carrier/Ring
  - D5/S0/Carrier/Conj
  - D5/S0/Carrier/Norm
  - D5/S0/Carrier/Units
  - D5/S1/Scale/Units
  - D5/S1/Scale/UnitGroup
  - D5/S1/Scale/Fibonacci
  - D5/S3/Arith/FibonacciRank
  - D5/S3/Arith/GoldenApparition
  - D5/S3/Arith/GoldenPrimeSplitting
  - D5/S3/Arith/GoldenPell
---

# Wall-Sun-Sun primes as a golden-unit lift problem

## Problem

Let `pi(m)` be the Pisano period, the least positive period of the Fibonacci
recurrence modulo `m`. The primary problem is whether there exists a prime `p`
with `pi(p) = pi(p^2)`. The paper also records the stronger conjecture that
infinitely many such primes exist.

Quoted from the introduction of arXiv:2603.25343v1:

> “A natural question was asked by Wall in his paper: Can there be a prime
> \(p\) such that \(\pi(p)=\pi(p^2)\)?”

> “It is known that up to \(10^{14}\), there are no such primes (cf. [16]).
> Still, using heuristics and probabilistic arguments, some authors conjecture
> the existence of infinitely many primes \(p\) satisfying
> \(\pi(p)=\pi(p^2)\) [7, 11].”

The same paper identifies the classical case with `d = 5` and says there are no
known `WSS(5)` primes.

Candidate formal statement, after defining `pisanoPeriod`:

```text
Existence:  ∃ p : Nat, Nat.Prime p ∧ pisanoPeriod p = pisanoPeriod (p^2)
Stronger:   Set.Infinite {p | Nat.Prime p ∧ pisanoPeriod p = pisanoPeriod (p^2)}
```

The paper states the difficulty:

> “The question of Wall for these sequences is related to certain deep
> arithmetic properties of real quadratic fields.”

It makes this precise for its generalized recurrence: equality of the periods
modulo `p` and `p^2` corresponds, subject to stated hypotheses, to failure of
`p`-rationality of the associated real quadratic field. This is why the global
existence question is not a routine finite-period exercise.

## Motivation

- Multiplication by `phi` on the basis `(1, phi)` is the Fibonacci matrix.
  Frozen `Scale/Fibonacci` already expresses powers of `phi` in Fibonacci
  coordinates.
- `GoldenApparition` and `FibonacciRank` control the first Fibonacci zero modulo
  a prime and the `p ± 1` Frobenius index; `GoldenPrimeSplitting` supplies the
  split/inert division according to 5 modulo `p`.
- The period can therefore plausibly be re-expressed as an order of the reduced
  golden unit or Fibonacci matrix. Equality at `p` and `p^2` is then an
  exceptional failure of the usual order multiplication by `p` under lifting.
- The first reachable theorem is not existence. It is an exact bridge among the
  pair recurrence period, the order of the Fibonacci matrix, and the order of
  `phi` in an appropriate golden algebra modulo `p^e` for `e = 1, 2`.

## Gap

- No frozen `pisanoPeriod` or recurrence-period API.
- `GoldenApparition` works modulo a prime; there is no golden algebra modulo
  `p^2` and no Hensel or p-adic order-lift theorem.
- There is no `p`-rational field or p-adic logarithm machinery.
- PID/UFD facts and the global unit classification alone do not decide the
  exceptional local lift.

## Route

1. Define the Fibonacci matrix `A = [[0,1],[1,1]]` over `ZMod m`; prove that
   `pi(m)` is its multiplicative order by tracking `(F_n, F_{n+1})`.
2. Define the reduction of `GoldenInt` over `ZMod m` and identify multiplication
   by `phi` with `A`.
3. For `r = pi(p)`, write the first lift as `A^r = I + pB (mod p^2)`. Prove
   `pi(p^2) = pi(p)` if and only if `B = 0 (mod p)`, and that otherwise the
   period acquires the expected factor `p`.
4. Use the frozen split/inert and apparition results to reduce the required
   congruence to a Fibonacci/Lucas quotient modulo `p`, separately in the two
   Legendre-symbol cases.
5. Only after those bridge theorems exist should a theorist choose between a
   conditional nonexistence theorem for a prime class, a density heuristic, or
   the global Wall question. Do not jump from a finite scan to existence.

## Falsifier

The existential Wall question has no honest finite falsifier. A proof that no
prime can satisfy the equality would refute it; a proof of finiteness would
refute only the stronger infinitely-many conjecture.

The proposed bridge is finitely falsifiable: find a prime `p` for which the
directly computed pair period disagrees with the order of the Fibonacci
matrix/golden unit, or for which `A^pi(p) = I (mod p^2)` disagrees with
`pi(p^2) = pi(p)`.

## Evidence

Implement three independent exact calculations for every prime `p < 10^6`,
excluding and separately reporting ramified and small cases:

1. direct pair-state Pisano periods modulo `p` and `p^2`;
2. fast-doubling checks of `F_r mod p^2` and `F_{r+1} mod p^2` at `r = pi(p)`;
3. matrix exponentiation of `A^r mod p^2` and the first-lift matrix `B mod p`.

Receipt fields should include `p`, `legendreSym 5 p`, `rank`, `pi_p`, `pi_p2`,
`F_r mod p^2`, `F_(r+1)-1 mod p^2`, and agreement of all three formulations.
This is bridge validation, not evidence that the global existential is false.

## Triage

`wall`. The repository is unusually close to the mod-`p` side, but the decisive
`p` to `p^2` lift is exactly the missing deep layer.

## ASSUMED-UNVERIFIED

- Whether the open problem was resolved after arXiv v1 is unverified; this
  records the paper's statement, not the entire later literature.
- The order of the reduced golden unit matches the chosen Pisano-period
  convention without a factor of 2 or a special case; that must be proved, not
  assumed.
- A useful local quotient criterion can be stated entirely with the current
  `GoldenInt` coordinate model.
- Any novelty of the proposed bridge lemmas is unassessed and belongs to the
  theorist's search step.

## FPD. Recurrence-level square transport and maximal-prime descent

### FPD.1 Original objects and the square-factor threshold

Use the original Fibonacci recurrence F_0=0, F_1=1 and
F_(n+2)=F_n+F_(n+1). A positive integer M is powerful when every prime
p dividing M also satisfies p^2|M. Thus one is powerful. In the source
this is the existing `PowerfulDivisorTransform.Powerful` predicate.
Put E={1,2,6,12}. For an odd prime p different from five, write
chi(p)=(p/5)=(5/p), and N(p)=p-chi(p). The standard WSS square condition
is p^2|F_(N(p)). Index primes and value-primes are different variables.

**Theorem FPD1.** For every prime p, positive n, and natural k, if
p|F_n, then

$$
\boxed{p^2\mid F_{nk}\quad\Longleftrightarrow\quad
       p^2\mid F_n\ \text{or}\ p\mid k.}
$$

This includes p=2 and k=0. It does not assume any initial valuation.

**Proof from the recurrence.** In R=Z/(p^2), put f=F_n, g=F_(n+1) and
c=F_(n-1). Then g=c+f and f^2=0. The Fibonacci addition formulas imply,
by simultaneous induction on k>=0,

$$
F_{n(k+1)}=(k+1)fg^k,\qquad
F_{n(k+1)+1}=g^{k+1}\quad\text{in }R.
$$

For the first induction step the new coordinate is
(k+1)fg^k c+g^(k+1)f. Replacing c by g-f gives
(k+2)fg^(k+1)-(k+1)g^k f^2, as required. The second new coordinate is
(k+1)f^2g^k+g^(k+2), also as required. The initial pair is (f,g).
Consecutive Fibonacci coprimality shows gcd(p,g)=1. Consequently, for
positive k, p^2|F_(nk) exactly when p^2|k F_n. Write F_n=p u and cancel
one p in the integers. Primality gives p|ku exactly when p|k or p|u.
The latter is equivalent to p^2|F_n. At k=0 both sides are true.

In particular, if p does not divide k, square divisibility is exactly
preserved between F_n and F_(nk). If p divides F_n simply and p does
not divide k, it still divides F_(nk) simply. A square produced solely
by multiplying the index by p is not an initial WSS exception.
For example F_7=13, 13^2|F_91, but F_14/13=29=3 modulo thirteen.

### FPD.2 The small-support case is completely eliminated

**Lemma FPD2.** If m>0 has no prime divisor greater than five, then

$$
\boxed{F_m\text{ powerful}\quad\Longleftrightarrow\quad m\in E.}
$$

**Proof.** The exact small values are

$$
F_5=5,\quad F_8=3\cdot7,\quad F_9=2\cdot17,
\quad F_{25}=5^2\cdot3001.
$$

The number 3001 is prime, by trial division through its square root,
which is less than55. If 25|m, the factor3001 remains simple in F_m by
FPD1, since it cannot divide this small-support index. Thus 25 does not
divide m. If 5|m, write m=5k. The preceding exclusion makes 5 not divide
k; FPD1 at F_5 then gives another simple factor, a contradiction.
Likewise 9|m preserves the simple prime17 from F_9, and 8|m preserves
seven from F_8. Hence a powerful value forces 5 not dividing m,
9 not dividing m and 8 not dividing m. Unique factorization now gives
m|12. The six positive divisors of12 are1,2,3,4,6,12. Indices3 and4
give the simple values2 and3, and the four remaining values are1,1,8,144,
all powerful. This proves both directions without an external valuation
formula or a classification of perfect powers.

### FPD.3 Prime-index factors escape the index support

**Lemma FPD3.** Suppose ell>=7 is prime and p is a prime divisor of
F_ell. Then the least positive Fibonacci zero index for p is ell, and
p>ell.

**Proof.** If p|F_j, strong divisibility gives
p|gcd(F_ell,F_j)=F_(gcd(ell,j)). Unless ell|j, primality of ell makes
that greatest common divisor one, impossible for p. Thus every zero
index is a multiple of ell. The initial zero at ell proves exact rank.

The cases p=2,5 are excluded by their zeros at indices3,5 respectively.
The existing golden Frobenius/rank theorem gives ell|p-1 or ell|p+1.
In the first case p>ell immediately. In the second, if p<=ell, the only
positive multiple of ell that can equal p+1 is ell itself. This gives
p+1=ell, impossible because both primes are odd. Thus p>ell in both
cases. No lower bound on the value-primes is assumed as an input.

### FPD.4 Constructive descent to a maximal prime-index WSS block

**Theorem FPD4.** If m>0, m is outside E, and F_m is powerful, then
there exists a prime ell>=7 such that

$$
\boxed{
\ell\mid m,\qquad
\forall q\text{ prime},\ q\mid m\Longrightarrow q\le\ell,
\qquad F_\ell\text{ is powerful}.
}
$$

Moreover every prime p dividing F_ell satisfies

$$
\boxed{p>\ell,\qquad p^2\mid F_{N(p)}.}
$$

**Proof.** By FPD2, m has a prime factor greater than five. Choose its
largest prime factor ell. It is at least seven. For each prime p|F_ell,
FPD3 gives p>ell, so p does not divide m. Write m=ell k. Fibonacci
divisibility gives p|F_m; powerfulness gives p^2|F_m. In FPD1 the
alternative p|k is impossible because k|m. Therefore p^2|F_ell.
This proves powerfulness of the entire prime-index block.

FPD3 gives its actual entry point ell. Apply the golden rank bound to
obtain ell|N(p), and then F_ell|F_(N(p)). Thus the square divisibility
also holds at p's own signed Frobenius index. Since p>ell>=7, the small
and ramified primes are automatically absent from this endpoint.
The theorem does not assert that the index-prime ell is WSS.

### FPD.5 Consequences and the remaining open arithmetic

**Corollary.** The following two assertions are equivalent:

$$
\begin{aligned}
&\forall m>0,\quad F_m\text{ powerful}\Longrightarrow m\in E;\\
&\forall\ell\ge7\text{ prime},\quad F_\ell\text{ is not powerful}.
\end{aligned}
$$

If the first assertion fails, its least counterexample index is prime
and at least seven.

**Proof.** The forward implication specializes to prime indices. For
the reverse, a nonclassical counterexample would descend by FPD4 to a
prime-index counterexample. For the least one, the descending prime
ell satisfies ell<=m and is itself a counterexample, so minimality
forces ell=m. Neither assertion is established by this equivalence.

For a prime index ell>=7, the existence of a simple prime divisor of
F_ell is equivalent to the existence of a non-WSS prime of exact rank
ell. Indeed, FPD3 supplies the exact rank, and ell|N(p) with p not
dividing N(p)/ell allows FPD1 to identify the two square-divisibility
conditions. Thus a remaining target is an independent simple-factor
existence theorem at prime indices. A primitive-prime theorem only
supplies a prime with that rank and does not assert exponent one.

Absence of all WSS primes would imply the first classification above,
since every nontrivial prime-index Fibonacci value has a prime divisor.
The classification's failure would produce WSS primes by FPD4. The
converse implication from a single WSS prime to failure of the powerful
classification is not asserted: the other factors of its rank block
may still be simple.

A prospective stronger lifting theorem is preservation of the entire
p-valuation under a multiplier coprime to p. The square-zero argument
already identifies its mechanism: at an actual initial depth e>=1,
F_n^2 vanishes modulo p^(e+1). Proving the corresponding depth theorem
requires retaining the nondivisibility at p^(e+1), the nonzero index and
the coprime multiplier. The present public transfer theorem certifies
the square threshold only; it does not silently assert that extension.

### FPD.6 Source roles and mathematical scope

FPD1 is a recurrence proof of a classical special case of the Fibonacci
valuation theory of Lengyel, recorded in Medina and Rowland,
*p-regularity of the p-adic valuation of the Fibonacci sequence*,
The Fibonacci Quarterly53(2015),265-271, Theorem1.4,
https://arxiv.org/abs/0910.2907 . The source proof here does not use that
theorem as an axiom or a lifting hypothesis. FPD4 develops the earlier
ordinary PBC.2 reduction from PR7708 using this explicitly proved local
step and the dev FibonacciRank owner.

Bates, Jesubalan, Lee, Lu and Shim, *Powerful Fibonacci polynomials over
finite fields*, arXiv:2601.02664v1 (2026), Theorem1.2 and Section2.1,
https://arxiv.org/html/2601.02664v1 , classify a polynomial problem over
finite fields and explicitly distinguish the conditional integer
powerful-number problem. A finite-field polynomial multiplicity does
not determine divisibility of an evaluated integer by p squared.
Their theorem is contextual prior work, not an input to FPD1-FPD4.

The companion sources are `FibonacciDepth/PrimeSquareTransport.lean`
and `FibonacciDepth/PowerfulPrimeDescent.lean`, each with an authored
Scribe. The latter uses the existing Powerful predicate and the actual
signed Frobenius index. They provide complete proof-script candidates;
no kernel acceptance is asserted here. The full classification and WSS
existence remain open targets of this line, not conclusions of FPD4.
