---
slug: bfrac-fracfactorial
bibkey: bala2016integerfactorials
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral.result
url: https://oeis.org/A276102
---

# Bala's fifth-index fractional-factorial integrality

## Problem

Peter Bala's OEIS [A276102](https://oeis.org/A276102/internal) states:

> a(n) = (6*n)!*(n/5)!/((3*n)!*(2*n)!*(6*n/5)!).

> This is only conjecturally an integer sequence.

In *Some integer ratios of factorials* (2016), page 1 defines $x!=\Gamma(x+1)$; page 5 states that the third-index and fifth-index samplings “are also integral for n ≥ 0.” The fifth-index assertion is

$$\forall n\in\mathbb N,\quad \exists z\in\mathbb Z,\quad
\frac{(6n)!\,\Gamma(n/5+1)}{(3n)!(2n)!\,\Gamma(6n/5+1)}=z.$$

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A276102's displayed ratio | `OeisA276102BalaFifthIndexIntegral.a` | Literal factorial and Gamma expression, with natural factorials cast to the reals. |
| Fractional factorials mean $\Gamma(x+1)$ | `Real.Gamma` in `a` | Real division by five; no floors replace fractional arguments. |
| Every nonnegative integer index | `claim` quantifies over `n : ℕ` | Includes zero; no residue or size restriction. |
| Integral value | `claim` quantifies over `z : ℤ` | Equality to the real cast of that integer. |
| The complete conjecture | `OeisA276102BalaFifthIndexIntegral.result` | Unconditional proof of `claim`. |

The dropped or weakened source-clause set is empty. The parameter systems and progression product in `OeisA276101BalaThirdIndexIntegral` organize the proof and introduce no hypothesis into the fifth-index claim.

## Motivation

The settling declaration is `D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral.result`, with admission basis `open-problem-resolution (#21666; Proved)`, generality `I` and `utility: none`. The statements are unbounded identities and divisibilities; no fixed numerical certificate supplies the proof.

## Gap

The complete external conjecture is preregistered in [#21666](https://github.com/the-omega-institute/trureturing/issues/21666). The literature screen found no complete settlement in the sources it inspected. Its completeness and priority are `ASSUMED-UNVERIFIED`.

## Route

Write $P_{d,L}(n)=\prod_{k=0}^{Ln-1}(n+d(k+1))$. The parameter tuples $(d,M,B,C,L)$ are $(3,10,5,2,3)$ and $(5,6,3,2,1)$.

The Gamma recurrence gives

$$\frac{\Gamma(n/d+1)}{\Gamma((1+dL)n/d+1)}=
\frac{d^{Ln}}{P_{d,L}(n)}.$$

For $d\nmid n$, prime valuations show $(Bn)!(Cn)!P_{d,L}(n)\mid(Mn)!$. For $d\mid n$, the ratio reduces to the ordinary factorial quotient $(30m)!m!/((15m)!(10m)!(6m)!)$. `BalaChebyshevFiveDivisibility.bala_five_integrality`, used by `ordinary_dvd`, supplies the stronger ordinary divisibility with an additional factor $5m+1$ in the divisor. `OeisA347854BalaHalfIndexIntegral.gamma_shift_product` supplies the Gamma recurrence product, and `OeisA347855BalaThirdIndexIntegral.padic_finset_prod` and `padic_eq_card` supply the valuation expansions. These are reused at their original owners.

## Falsifier

A natural index whose displayed real ratio is not the cast of an integer would refute the conjecture. `result` proves the complete assertion for every natural index; finite checking is supplementary evidence.

## Evidence

The settling source and mirror are `D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral.lean` and its corresponding Blueprint Scribe. The shared source is `OeisA276101BalaThirdIndexIntegral.lean`. Every declaration is classified `bind-only`; mathematical admission uses the preregistered external open-problem-resolution basis. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

Escape audit unfinished: [#21712](https://github.com/the-omega-institute/trureturing/issues/21712). This includes the two results, the four public shared helpers and the three published owner helpers. A faithful family realization, source bridge and intervention/sensitivity evidence have not been supplied; no validated registration is claimed.

### Exact experiment

[Experiments at `8ceaa46e4861ff7dec4abcd01a9d0d69881d9564`](https://github.com/the-omega-institute/trureturing-experiments/tree/8ceaa46e4861ff7dec4abcd01a9d0d69881d9564/docs/reports/bala-fractional-factorial) contains `check.py`. The command `python3 /Users/auric/.sshx/3c1ba4c14cb6f17fb15467ff/attempt-1/experiment-check.py` runs its byte-identical extracted source: exit 0; SHA-256 `060cda1dbb4c8ae89c563d27351d26c29e9b8915836bab1f759dea7290a8b438`.

For each of A276100, A276101 and A276102, the checker reproduces the first six source terms and checks exact Gamma-recurrence/progression agreement and positive integrality for $n=0,\ldots,400$ (401 values per family). It checks 15,714 exact translated-floor identities at $n=0,\ldots,80$ and coprime $q=2,\ldots,100$, and the six displayed A364175 values. These are finite computations, not proofs of uniform extensions.

## Triage

### What the settlement shows

1. **Kernel-checked:** both original universal integrality claims, including $n=0$, are proved by `OeisA276101BalaThirdIndexIntegral.result` and `OeisA276102BalaFifthIndexIntegral.result`.
2. **Kernel-checked:** for both listed parameter systems, the arithmetic-progression bound holds for every natural $n$ and every positive $q$ coprime to $d$, including residue zero. This is the private `progression_floor_bound` theorem in `OeisA276101BalaThirdIndexIntegral`, consumed by `nonmultiple_dvd`; its scope is stronger than the nonmultiple branch used by either result.
3. **Kernel-checked:** if $d\nmid n$, then $(Bn)!(Cn)!P_{d,L}(n)\mid(Mn)!$, before multiplication by $d^{Ln}$. This is `OeisA276101BalaThirdIndexIntegral.nonmultiple_dvd` for either parameter system.
4. **Kernel-checked:** the displayed Gamma reduction holds for every positive natural $d$ and all natural $L,n$, by `OeisA276101BalaThirdIndexIntegral.gamma_ratio`. **Proved in prose:** its specialization makes both target ratios rational, because the progression is a nonzero natural number and the remaining factors are natural factorials and powers.
5. **Computed:** the exact checker passes through $n=400$ and on the finite floor-identity grid specified in the experiment entry, with exit 0 and the recorded SHA-256. No uniform assertion follows from this computation alone.
6. **Open:** no generating-function algebraicity result or theorem for arbitrary sampling denominators is supplied. The two integrality conjectures in Bala's source are settled; its separate algebraicity questions receive no conclusion from these results.

The decisive mechanism is cancellation of the common fractional Gamma residues into a rational progression product, followed by prime-power counting. Coprimality gives the progression count away from the sampling prime; the nonmultiple branch excludes that prime from every progression factor, and the multiple branch uses ordinary factorial divisibility. The positive-$q$ bound includes $q=1$; the experiment grid starts at $q=2$.

## ASSUMED-UNVERIFIED

The literature screen covers the OEIS entries, Bala's note, Radcliffe's A364175 note, integer-slope results of Bober and Rodriguez-Villegas, Akbik's factorial-divisibility paper and the related translated-Landau notes identified in #21666. No full target settlement was located within that screen. Literature completeness and priority remain `ASSUMED-UNVERIFIED`; blocked or unusable index responses are not negative search results. The source is OEIS-only, has no located DOI or arXiv identifier, and uses the stable OEIS PDF locator.
