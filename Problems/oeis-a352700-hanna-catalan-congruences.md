---
slug: oeis-a352700-hanna-catalan-congruences
bibkey: hanna2022a352700
doi: null
url: https://oeis.org/A352700
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.result
---

# Hanna's OEIS A352700 Catalan power-series and modular-coefficient conjectures

## Problem

Paul D. Hanna's [OEIS A352700](https://oeis.org/A352700) (revision `#7`, March 31, 2022; unpaginated), NAME, defines the sequence by:

> G.f.: Sum_{n>=0} binomial((n+1)*(2*n+1),n)/(2*n+1) * x^n / C(x)^(n*(2*n+1)+1), where C(x) = 1 + x*C(x)^2 is the Catalan function (A000108).

Its COMMENTS state the six numbered conjectures:

> Conjectures: given g.f. A(x), let C(x) = (1 - sqrt(1-4*x))/(2*x) be the Catalan power series (A000108), then
> (1) A(x)^3 = A(x^3) (mod 3),
> (2) A(x) = C(x) + x^2*C(x)^3 (mod 3) = (2 - x)*C(x) - 1 (mod 3),
> (3) A(x) = C(x) (mod 2),
> (4) a(n) = binomial(2*n+1,n)/(2*n+1) + 3*binomial(2*n-1,n-2)/(2*n-1) (mod 3) for n >= 0,
> (5) a(n) = 2*A000108(n) - A000108(n-1)  (mod 3) for n >= 1,
> (6) a(n) = A000108(n) (mod 2) for n >= 0.

The published OFFSET is `0,3`. Its EXAMPLE field records the coefficient expansion of $C(x) + x^2 C(x)^3$, under which the second term $3\binom{2n-1}{n-2}/(2n-1)$ vanishes for $n < 2$ by the negative-lower-index binomial convention $\binom{2n-1}{n-2} = 0$, and its PARI PROG defines $a(n)$ by the finite degree-$n$ truncation over $0 \le m \le n$. The [Library note](../Library/RecurrenceComposition/hanna2022a352700.md) records the source and exact integer divisibility of each weight and Raney quotient. Preregistration: [#23834](https://github.com/the-omega-institute/trureturing/issues/23834).

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Weight $\binom{(m+1)(2m+1)}{m}/(2m+1)$ | `weight m` | Exact natural quotient; $(2m+1) \mid \binom{(m+1)(2m+1)}{m}$ proved for every $m \in \mathbb N$. |
| Catalan generating series $C(x) = 1 + x C(x)^2$ and $C(x)^{-1}$ | `catalanZ`, `catalanInvZ` | Integral formal series in $\mathbb Z[[X]]$ with $[X^n]C(X) = \operatorname{catalan}(n)$ and multiplicative unit inverse. |
| Defining series $A(x)$ and $a(n) = [x^n]A(x)$ | `coeffA`, `seriesA` | Finite $(X)$-adically exact sum over $0 \le m \le n$ in $\mathbb Z$ and $\mathbb Z[[X]]$. |
| Reductions modulo $2$ and $3$ | `seriesMod p`, `catalanMod p` | Coefficientwise ring-homomorphism reductions in $(\mathbb Z/p\mathbb Z)[[X]]$. |
| Second term of `(4)` under $\binom{2n-1}{n-2}=0$ for $n < 2$ | `raneyTerm n` | Zero for $n < 2$ and exact natural quotient $(3\binom{2n-1}{n-2})/(2n-1)$ for $n \ge 2$. |
| Conjectures `(1)`–`(6)` | Six conjuncts of `claim`, proved by `result` | Exact conjunction of `(1)` `(seriesMod 3)^3 = (seriesMod 3)(X^3)`, `(2)` both mod-$3$ series identities, `(3)` mod-$2$ series identity, `(4)` mod-$3$ Raney congruence for all $n \ge 0$, `(5)` mod-$3$ Catalan difference congruence for all $n \ge 1$, and `(6)` mod-$2$ Catalan congruence for all $n \ge 0$. |

## Motivation

Each coefficient $a(n)$ aggregates unboundedly varying inverse Catalan powers $C(X)^{-(m(2m+1)+1)}$ weighted by quadratic binomial quotients, yet its reductions modulo $2$ and modulo $3$ collapse to linear combinations of Catalan numbers at every degree. Finite coefficient inspection cannot establish these all-degree congruences across arbitrary $2$-adic and $3$-adic scales.

## Gap

The source and literature screen recorded in [#23834](https://github.com/the-omega-institute/trureturing/issues/23834) inspected OEIS A352700 revision `#7` and related Catalan/Raney entries A000108, A001764, A352698, A352699, A352701 and A352702, together with bounded web and literature queries for `A352700` and its defining sum. No prior proof or settlement reference for `(1)`–`(6)` was found in the inspected scope. Global literature completeness, global proof novelty, and continued external open status are `ASSUMED-UNVERIFIED`.

## Route

Introduce $\zeta(X) = X(1+X)^{-2}$ and $q(X) = C(X) - 1$ in $\mathbb Z[[X]]$. Because $C(X) = 1 + X C(X)^2$, direct substitution gives $\zeta(q(X)) = X$, and `SignedCatalanCubicSubstitutionModThree.inverse_exists` yields the reverse identity $q(\zeta(X)) = X$, hence $C(\zeta(X)) = 1 + X$ and $C(\zeta(X))^{-1} = (1+X)^{-1}$. Substituting $\zeta(X)$ into $(X)$-adic truncations of $A(X)$ identifies $A(X) = B(q(X))$, where

$$
B(X) = \sum_{m \ge 0} w(m) X^m (1+X)^{-(m+1)(2m+1)}, \qquad
[X^n]B(X) = \sum_{m=0}^n (-1)^{n-m} w(m) \binom{2m(m+1)+n}{n-m}.
$$

Modulo $2$, Pascal's identity and binomial absorption split every $m = k+1 \ge 1$ summand of $[X^{N+2}]B(X)$ into two quadratic binomial sums $\sum_{j=0}^L \binom{L}{j}\binom{2(j+c)(j+c+1)+d+L}{L}$ with $L \in \{N+1, N+2\}$. Choosing $k$ with $2^k \le L < 2^{k+1}$ and pairing $j$ with $j + 2^k$ leaves both binomial factors invariant modulo $2$ because $2(j+2^k+c)(j+2^k+c+1) \equiv 2(j+c)(j+c+1) \pmod{2^{k+1}}$, annihilating every pair. Hence $B(X) \equiv 1 + X \pmod 2$ and $A(X) \equiv 1 + q(X) = C(X) \pmod 2$, proving `(3)` and `(6)`.

Modulo $3$, binomial absorption $r\binom{3ru}{r} = 3ru\binom{3ru-1}{r-1}$ and base-$3$ Lucas decomposition prove $w(m) \equiv 0 \pmod 3$ whenever $m \ge 1$ and $m \not\equiv 1 \pmod 3$, while $w(3M+1) \equiv 2\binom{6M(M+1)+1+M}{M} \pmod 3$. For $[X^n]B(X)$ with $n \ge 2$, every $m \ge 1$ summand vanishes termwise when $n \not\equiv 1 \pmod 3$ by base-$3$ digit mismatch, whereas for $n = 3N+1$ ($N \ge 1$) binomial absorption reduces the $m = 3M+1$ slice to $2\sum_{M=0}^N (-1)^{N-M}\binom{N}{M}\binom{6M(M+1)+1+N}{N}$. Choosing $k$ with $3^k \le N < 3^{k+1}$ and grouping $M, M+3^k, M+2\cdot 3^k$ fixes the quadratic upper argument modulo $3^{k+1}$ and factors out $\binom{d}{0} - \binom{d}{1} + \binom{d}{2} \equiv 0 \pmod 3$ for $d = \lfloor N/3^k \rfloor \in \{1,2\}$. Thus $B(X) \equiv (1+X)^{-1} + 2X \pmod 3$, so $A(X) \equiv C(X)^{-1} + 2(C(X)-1) = (2-X)C(X) - 1 = C(X) + X^2 C(X)^3 \pmod 3$, proving `(2)`, `(1)` via `SignedCatalanCubicSubstitutionModThree.prime_power_subst`, and `(4)`–`(5)` via exact Catalan identities $\binom{2n+1}{n}/(2n+1) = C_n$ and $\operatorname{raneyTerm}(k+2) + C_{k+1} = C_{k+2}$.

## Falsifier

Any index $n \ge 0$ (or $n \ge 1$ for `(5)`) at which $a(n)$ failed the stated modulo-$2$ or modulo-$3$ congruence, or any coefficient mismatch in $(\mathbb Z/2\mathbb Z)[[X]]$ or $(\mathbb Z/3\mathbb Z)[[X]]$, would contradict `result`. Alternative non-zero interpretations of $\binom{2n-1}{n-2}$ at $n \in \{0,1\}$ lie outside the EXAMPLE-authenticated negative-lower-index convention encoded in `raneyTerm`.

## Evidence

`D5.S3.Combinatorics.PowerSeries.HannaA352700CatalanCongruences.result` proves the complete six-part `claim`. Its admission basis is `open-problem-resolution (#23834; Proved)`, its generality is `G`, and its utility is `none`. It is the module's sole public theorem audit target; the nine public definitions are source objects and consumed reductions mirrored in Blueprint.

The same-delivery Reg mirror `Reg/D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.lean` compiles a `DependentFamily.Registration` and `Contract.Registration` retaining `coeffA : ℕ → ℤ` and all six modular series and coefficient conjuncts. Its four-slot binding is unfinished: [#23867](https://github.com/the-omega-institute/trureturing/issues/23867). The current scoped producer records `declared_unresolved`, `IE-C050 ClosedTruthReadout`, `reason=unclassified_form`, `rule=source.selection_missing`, with `certificate: null` and `continuation := .unknown`. No `declared_validated` registration is claimed; delivery uses `CLAUDE.md` §3.9's linked-issue disclosure.

## Triage

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| Registered six-conjecture conjunction `(1)`–`(6)` | Proved, kernel-checked `D5/S3/Combinatorics/PowerSeries/HannaA352700CatalanCongruences.result` | All six modular power-series and all-index coefficient congruences of OEIS A352700. |
| Compositional reduction and Frobenius annihilation | Proved, kernel-checked private `seriesA_eq_subst`, `mod_two_quadratic_choose_sum_zero`, `seriesB_mod_two`, `mod_three_quadratic_choose_sum_zero`, `seriesB_mod_three` | Exact identity $A(X) = B(C(X)-1)$ in $\mathbb Z[[X]]$ and complete mod-$2$ and mod-$3$ evaluations of $B(X)$. |
| Companion odd-position remark in A352700 COMMENTS | Open, unformalized remark outside registered `claim` | `"Odd terms seem to occur only at positions 2^n-1 for n >= 0"` is a separate unnumbered remark not included in `claim`. |
| Four-slot Reg audit | Open, current scoped producer and #23867 | `declared_unresolved` (`IE-C050 ClosedTruthReadout`, `rule=source.selection_missing`); no certificate or `declared_validated` claim. |

### What the settlement shows

The kernel-checked `result` establishes all six numbered conjectures `(1)`–`(6)` of Paul D. Hanna in OEIS A352700 for every natural index $n$ (with $n \ge 1$ in `(5)`) and as formal power series over $\mathbb Z/2\mathbb Z$ and $\mathbb Z/3\mathbb Z$. The decisive mechanism is Lagrange-type substitution $\zeta(X) = X(1+X)^{-2}$ combined with $2^k$ pairing and $3^k$ three-way Frobenius grouping of quadratic binomial sums.

The unnumbered odd-support remark in A352700 COMMENTS, higher-modulus congruences for $A(X)$, and companion entries A352698–A352702 are not claimed as settled theorems of this module and receive no problem-resolution credit here.

## ASSUMED-UNVERIFIED

Global literature completeness, global proof novelty, and continued external open status beyond the bounded OEIS and web screen recorded in #23834. The four-slot Reg audit remains unfinished under #23867.
