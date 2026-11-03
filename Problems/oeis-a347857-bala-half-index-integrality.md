---
slug: oeis-a347857-bala-half-index-integrality
bibkey: bala2021fractionalfactorial
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral.result
url: https://oeis.org/A347857
---

# Bala's A347857 fractional-factorial integrality

## Problem

Peter Bala, OEIS [A347857](https://oeis.org/A347857), states:

> a(n) = (6*n)!/((3*n)!*(2*n)!) * (3*n/2)!/(5*n/2)!.

Fractional factorials mean $x! = \Gamma(1+x)$.
The integrality conjecture quantifies over every natural index, including zero.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The source's displayed ratio and product endpoints | `D5.S3.Arith.FactorialRatio.OeisA347857BalaHalfIndexIntegral.a` | Literal expression; natural factorials are cast to the reals. |
| Fractional factorials use Gamma | `OeisA347854BalaHalfIndexIntegral.ffact` | $x! = \Gamma(1+x)$; the natural-index factorials are `Nat.factorial`. |
| Integral for all natural indices | `D5.S3.Arith.FactorialRatio.OeisA347857BalaHalfIndexIntegral.claim` | For every $n\in\mathbb N$ there exists $z\in\mathbb Z$ whose cast equals the ratio. |
| The conjecture is true | `D5.S3.Arith.FactorialRatio.OeisA347857BalaHalfIndexIntegral.result` | Unconditional proof of the complete claim. |
| Proof-only arithmetic parameters | Consumed floor, divisibility and Gamma helpers | Internal parameters support the proof; they add no assumption to the conjecture. |

The dropped or weakened source-clause set is empty.

## Motivation

The settling GID is `D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral.result`.
The declaration uses admission basis `open-problem-resolution (#18695; Proved)`,
generality `I`, and `utility: none`. All declarations are symbolic, unbounded
identities, inequalities or divisibility statements, rather than fixed numerical
certificates or bounded enumerations.

## Gap

This tier-1 external conjecture is preregistered in
[issue #18695](https://github.com/the-omega-institute/trureturing/issues/18695).
The literature screen read the OEIS statements, Bala's *Some integer ratios of
factorials*, pp. 5–6, and Bober's Table 2. The source lists the fractional-index
integrality assertions without proofs. The integer-coefficient factorial-ratio
and $N$-integrality literature listed in the preregistration does not settle the
exact fractional-index assertions in the passages read. Literature completeness
is `ASSUMED-UNVERIFIED`.

**Prior settlement.** Roberto Blanco Gómez, *Supercongruences modulo p^(3k) and integrality for factorial ratios with fractional arguments, with proofs of conjectures of P. Bala*, Zenodo, [DOI 10.5281/zenodo.23426707](https://doi.org/10.5281/zenodo.23426707), record dated 2026-10-16, Corollary 1.5, proves this integrality. The record precedes the preregistration in #18695, which therefore did not concern an open problem. The Lean result in this repository is an independent kernel-checked proof of that published theorem, not a first resolution.

## Route

Legendre's formula converts factorial divisibility to inequalities between sums
of natural floor divisions. Periodic floor defects are nonnegative by division
into their breakpoint intervals. At even indices the half-index sequences are
integer factorial quotients. At odd indices the half-integer Gamma formula
cancels the common square-root factor and supplies a power of two. The
third-index Gamma recurrence supplies a power of three and a product of linear
factors. Indices divisible by three use the A347854 even denominator instead.
The auxiliary denominators specialize the common third-index divisibility
statement. These are the mechanisms of the delivered proofs; the explanatory
valuation language is not an additional theorem declaration.

## Falsifier

A natural index whose source-defined value is not the cast of an integer would
contradict `result`. The corresponding exact source expressions and all zero
indices remain in the quantifier domain. The stronger unscaled third-index
quotient is asserted integral only when $3\nmid n$.

## Evidence

The Lean module is [D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral.lean](../D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral.lean); the complete public proposition
is rendered by its Blueprint Scribe. The axiom closure of every public
declaration is contained in {`propext`, `Classical.choice`, `Quot.sound`}.

Experiment: [fractional-factorial exact arithmetic](https://github.com/the-omega-institute/trureturing-experiments/tree/768095c6e50e44440547f401c54866f9d982711a/docs/reports/oeis-a347854-a347858-bala-fractional-factorial-ratios).
The command `python3 check.py 300` at that directory exits 0; `check.py` SHA-256
is `37bd9cb7bf77ee694f56cc102c3bd745de1fea57ad2317ac73be112aaa675f74`. The five sequences are checked for $0\le n\le300$,
and $b(m),c(m)$ and their relations to A347855 for $0\le m\le100$.
The ten floor functions take values 0 and 1 on $j/360$, $0\le j<360$, with
their period-one checks. These finite readings do not replace the universal proofs.

The four-slot escape audit is unfinished for all 22 public theorem targets;
[issue #19874](https://github.com/the-omega-institute/trureturing/issues/19874)
names the missing enrolled-template, reconstruction and variation evidence.
No Reg mirror or validated registration is claimed.

### Declaration judgement

The D5 prerequisites are drawn from this seven-module delivery;
none is a pre-existing frozen dependency. The table reports the declarations of
this module after expansion of same-delivery helpers.

| Declaration | proof_shape | escape_witness | Consumers | Direct frozen dependencies |
| --- | --- | --- | --- | --- |
| `a` | bind-only | none | claim, even_formula, odd_formula, result | none |
| `claim` | bind-only | none | result | none |
| `even_dvd` | bind-only | none | result | none |
| `even_formula` | bind-only | none | result | none |
| `odd_dvd` | bind-only | none | result | none |
| `odd_formula` | bind-only | none | result | none |
| `result` | bind-only | none | settling result | none |

## Triage

### What the settlement shows

1. **Proved, kernel-checked:** all five original fractional-factorial sequences
   and both specified auxiliaries are integral at every natural index. Evidence:
   `D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.result`, `D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.result`, `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxBIntegral.result`, `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxCIntegral.result`, `D5/S3/Arith/FactorialRatio/OeisA347856BalaHalfIndexIntegral.result`, `D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral.result`, `D5/S3/Arith/FactorialRatio/OeisA347858BalaHalfIndexIntegral.result`.
2. **Proved, kernel-checked intermediate:** for $3\nmid n$,
   $$(2n)!\,n!\prod_{j=1}^n(n+3j)\mid(4n)!.$$
   Evidence: `D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.third_dvd`. This supplies A347855 away from multiples
   of three and both auxiliaries; no uniform claim at multiples of three is made.
3. **Computed, exact rational arithmetic at one index:** with
   $$R(n)=\frac{(4n)!}{(2n)!\,n!\prod_{j=1}^n(n+3j)},$$
   $R(3)=1540/9$ and $3^3R(3)=4620$. The pinned exact-arithmetic experiment
   checks A347855(3) against 4620, and the quotient relation divides this value
   by $3^3=27$. Explicitly, $R(3)=12!/(6!\,3!\,6\cdot9\cdot12)=1540/9$.
   This is a computed one-index value, not a separately kernel-checked equality.
   At multiples of three the integrality argument uses the A347854 even denominator.
4. **Proved in prose from the reductions, without separate Lean declarations:**
   at odd $n$, the half-index formulas express A347854, A347856 and A347857
   as $2^{2n}$ times an integer, and A347858 as $2^{8n}$ times an integer.
   In the Gamma quotient $\Gamma(1+rn/2)/\Gamma(1+sn/2)$, the pairs
   $(r,s)$ are $(1,3)$ for A347854/A347856, $(3,5)$ for A347857 and
   $(1,9)$ for A347858. It contributes $2^{(s-r)n}$; the odd-denominator
   divisibility proofs supply an integral remaining quotient. For $3\nmid n$, the Gamma
   recurrence and `third_dvd` express A347855 as $3^n$ times an integer.
   Thus the factors follow by multiplication of integers, with exactly these
   index restrictions. They are consequences of the proof, not additional
   public Lean statements.
5. **Open / outside scope:** the OEIS supercongruences, algebraicity questions,
   A295432's stronger auxiliary divisibility and any broader classification.
   The integrality premises are supplied by the seven results; no other source
   conjecture is thereby asserted proved.

## ASSUMED-UNVERIFIED

The literature search is not exhaustive. Four-slot registration evidence remains
unfinished under #19874. Finite experimental ranges are exactly those above.
