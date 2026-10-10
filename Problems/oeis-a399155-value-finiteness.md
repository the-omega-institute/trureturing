---
slug: oeis-a399155-value-finiteness
bibkey: dilkhush2026a399155
doi: null
url: https://oeis.org/A399155
triage: theorem
motivation_gids:
  - D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness.result
---

## Problem

Dilkhush's OEIS A399155 defines $a(n)=f(n)-g(n)$ using the smallest- and largest-prime-factor subtraction step counts. Its empirical observation is that each positive value is attained only finitely often. The exact assertion is preregistered in [#14993](https://github.com/the-omega-institute/trureturing/issues/14993): for every integer $v>0$, the set $\{n\in\mathbb N: n\ge2\text{ and }a(n)=v\}$ is finite.

The two walk definitions and their integer-valued difference are defined together in the finiteness module, reusing `CenteredReducedResidueProgressions.GreatestPrimeFactor`.

## Motivation

Nonnegativity does not exclude infinitely many repetitions of a fixed positive value. The finiteness question instead requires a lower bound tending to infinity along composite indices, together with a treatment of prime indices.

## Gap

The comparison $a(n)\ge0$ follows from the published OEIS A175126 smallest-factor formula $f(n)=(n-\operatorname{lpf}(n))/2+1$ and A309892 largest-factor bound $g(n)\le n/\operatorname{gpf}(n)$, as recorded in `Library/Words/oeis2026triage0909.md`. Those facts do not settle finiteness of positive fibers: when $n$ is a power of two, the direct largest-factor bound is only $g(n)\le n/2$, so it provides no growing lower bound on $a(n)$. The power-of-two case and uniform growth along composite indices require a further argument. The supplied A399155 source identifies positive-fiber finiteness as an empirical observation, and the existing repository triage does not treat it as settled. The proof below consumes the published facts as private helpers and makes no originality claim for them.

This implementation carries that source reading and the preregistration; it does not claim a fresh external search or exhaustive publication priority. A bounded prefix alone does not prove finite fibers on an unbounded domain.

## Route

At a prime index, each walk subtracts the index itself in one step, so $a(n)=0$. For every composite $n\ge6$, establish

$$6a(n)+3\lfloor\sqrt n\rfloor+3\ge n.$$

First establish the uniform bound $3g(n)\le n+1$ for every $n\ge6$. If the largest prime factor is at least three, this follows directly from the weighted bound $g(n)\operatorname{gpf}(n)\le n$. Otherwise that factor equals two. The smallest prime factor of $n/2$ is a prime divisor of $n$, so it is at most two and consequently equals two. Thus four divides $n$. The number $(n-2)/2$ is then odd and at least three; one of its prime divisors is odd and hence at least three, proving $\operatorname{gpf}(n-2)\ge3$. The recurrence gives $g(n)=1+g(n-2)$, and the weighted bound on the remainder yields $3g(n)\le3+(n-2)=n+1$. This argument needs no classification of integers whose largest prime factor is two.

For even composite $n$, the exact count $f(n)=n/2$ and the uniform bound give the displayed lower estimate. For odd composite $n$, its smallest prime factor $p$ satisfies $p\le\lfloor\sqrt n\rfloor$. The identity $f(n)=1+(n-p)/2$ and the same uniform bound give that estimate as well.

For a fixed positive integer value $v$, put $t=\lfloor\sqrt n\rfloor$. At a composite index at least six with $a(n)=v$, the inequalities $t^2\le n\le6v+3t+3$ imply $t\le6v+6$, and substitution gives $n\le24v+21$. Prime indices cannot realize $v$, and indices below six satisfy this final bound too. Thus the fiber is contained in $\{n\in\mathbb N:n\le24v+21\}$ and is finite. In the Lean natural-index bound the integer value is represented by `v.toNat`.

## Falsifier

A positive integer $v$ attained by infinitely many natural indices at least two would refute the assertion. A composite $n\ge6$ violating the displayed lower bound would invalidate this proof route. Prime indices with zero difference do not refute the positive-value assertion.

## Evidence

`D5.S3.Arith.Primes.PrimeFactorSubtractionValueFiniteness.claim` is exactly the assertion that every positive integer value has a finite fiber among natural indices at least two. The matching `result : claim` is the designated resolution declaration. The argument consumes the weighted largest-factor step bound and the exact smallest-factor counts as private helpers in the same module. The matching Blueprint result node declares a Proved resolution of this dossier slug.

## Triage

- [proved] The explicit lower bound $6a(n)+3\lfloor\sqrt n\rfloor+3\ge n$ along composite indices $n\ge6$, and finiteness of every positive-value fiber.
- [open] The exact list of $n$ with $a(n)=v$ for each value $v$.

## ASSUMED-UNVERIFIED

No fresh network search was performed because the implementation seat has no network. The source attribution and preregistration readings are carried from the supplied task and the existing repository triage. That triage does not claim the fiber-finiteness assertion solved; this absence is bounded to its searched scope. No claim of first-publication priority follows from those readings. The result excludes the zero-value fiber from its finiteness assertion and imposes no upper bound on the positive value $v$.
