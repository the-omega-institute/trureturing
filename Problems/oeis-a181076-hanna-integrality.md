---
slug: oeis-a181076-hanna-integrality
bibkey: hanna2010a181076
doi: null
url: https://oeis.org/A181076
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/HannaA181076Integrality.result
---

# Hanna's OEIS A181076 integrality conjecture

## Problem

Paul D. Hanna, [OEIS A181076](https://oeis.org/A181076), NAME and first COMMENTS line; [preregistration #30007](https://github.com/the-omega-institute/trureturing/issues/30007).

> G.f.: exp( Sum_{n>=1} [ Sum_{k>=0} C(n+k-1,k)^n *x^k ] *x^n/n ).
>
> Conjecture: this sequence consists entirely of integers.

The formal series are over $\mathbb Q[[x]]$. Write
\[
L=\sum_{n\ge1}\sum_{k\ge0}\binom{n+k-1}{k}^{n}\frac{x^{n+k}}{n},
\qquad A=\exp(L).
\]
The source conjecture is that every ordinary coefficient of $A$ is an integer.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The displayed logarithmic generating function | `D5.S1.Recurrence.Algebraic.HannaA181076Integrality.logarithm` | The coefficientwise finite diagonal uses the literal exponent $n$, the ordinary power $x^{n+k}$, and rational division by $n$. |
| The formal exponential | `D5.S1.Recurrence.Algebraic.HannaA181076Integrality.A` | `PowerSeries.subst logarithm (PowerSeries.exp ℚ)` over rational formal power series. |
| Entirely integers | `D5.S1.Recurrence.Algebraic.HannaA181076Integrality.claim` | $\forall m\in\mathbb N$, there is $z\in\mathbb Z$ with $[x^m]A=z$ in $\mathbb Q$, including $m=0$. |
| Conjecture holds | `D5.S1.Recurrence.Algebraic.HannaA181076Integrality.result` | Exactly `claim`, with no extra hypothesis, factorial normalization, convergence condition, or degree bound. |

The immutable source is [the OEIS data revision](https://raw.githubusercontent.com/oeis/oeisdata/de48538e52019dc132e250666b0d677b40045ceb/seq/A181/A181076.seq); the quoted entry and CC-BY-SA-4.0 attribution are retained in the [source note](../Library/RecurrenceAlgebraic/hanna2010a181076.md).

## Motivation

This settlement gives an all-degree ordinary-coefficient theorem for Hanna's exact A181076 exponential. The neighboring A181070 and A181074 integrality results supply the shared dilation mechanism, while the present exponent remains the source's binomial power $n$.

## Gap

The preregistration and bounded source search identify the exact OEIS conjecture and report no solution in the inspected literature and repository scope. The source entry, its immutable data revision, and the current source-equivalent formal interpretation agree. The bounded screen does not establish worldwide literature completeness or publication priority.

## Route

Set $F(0,k)=0$ and $F(n,k)=\binom{n+k-1}{k}^{n}$ for $n>0$. The consumed negative-binomial divisibility theorem gives $n\mid k\binom{n+k-1}{k}$; `divPower` raises this to $n\mid kF(n,k)$. For a prime $p$, positive $n$, and $q=p^{v_p(n)+1}$, the consumed A181074 congruence gives
\[
q\mid F(pn,pk)-\binom{n+k-1}{k}^{pn}.
\]
For the same integer $b=\binom{n+k-1}{k}$, `ZMod.pow_card` gives $p\mid b^p-b$, and `HannaSelfSubstitutionIntegrality.power_lift` gives $q\mid b^{pn}-b^n$. Adding the two divisibilities yields the dilation congruence required by `HannaA181070Integrality.integralGeneric`. Its `literalUnbounded` bridge identifies the coefficientwise diagonal with the source logarithm. The zero-index totalization contributes zero after rational division, the logarithm has constant coefficient zero, and the formal exponential therefore has constant coefficient one. The final natural-degree split proves the exact all-degree claim.

## Falsifier

An ordinary degree $m$ with no integer representative for the coefficient of the displayed $A$ would contradict `result`. A finite coefficient computation, a factorial-scaled coefficient, a bounded $k$-range such as $k\le n$, or a changed exponent would concern a different statement and would not refute this result.

## Evidence

The canonical mathematical source is `D5/S1/Recurrence/Algebraic/HannaA181076Integrality.lean`, with public `logarithm`, `A`, `claim`, and `result`. Its frozen state is `Golden/Frozen/state/D5/S1/Recurrence/Algebraic/HannaA181076Integrality.lean.json`. The result is a bind-only application of the frozen divisibility, congruence, lifting, and generic integrality suppliers; its admission basis is `open-problem-resolution`, with no escape witness or downstream mathematical consumer required.

The owning Blueprint Scribe is `Blueprint/D5/S1/Recurrence/Algebraic/HannaA181076Integrality.scribe.cs`; it displays the complete source definitions, quantified claim, proof route, source note, and a `Proved` open-problem resolution for this result. The corresponding Reg source is `Reg/D5/S1/Recurrence/Algebraic/HannaA181076Integrality.lean`; its exact source-equivalence registration remains the current `declared_validated` audit for the result. The supplier public surfaces are canonically repinned from their current compiled declarations; their original theorem statements and proofs are unchanged.

## Triage

Tier 1 external OEIS conjecture, preregistered in issue #30007. The resolution is `proved` by the exact `result` declaration. The module is admitted under the external open-problem-resolution basis; it has no digestion atom and no utility instance.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `result` | bind-only | none | open-problem-resolution |

### What the settlement shows

- **Proved, kernel-checked:** every ordinary coefficient of the exact A181076 formal exponential is an integer for every natural degree, including degree zero.
- **Proved, kernel-checked:** the source logarithm is identified with its finite diagonal coefficient sum, and the generic integrality criterion applies with the exponent-$n$ array described above.
- **Proved in the proof route:** the prime-power dilation congruence is obtained by adding the consumed negative-binomial congruence to the power-lifting congruence for $b^p-b$; this covers every prime and $k=0$.
- **Proved in the proof route:** the constant coefficient is one because the logarithm has constant coefficient zero and the formal exponential has constant coefficient one.
- **Open:** extensions to other exponents, altered diagonal weights, analytic convergence, asymptotic growth, or implications between neighboring Hanna sequences are outside this settlement.

## ASSUMED-UNVERIFIED

The bounded literature search does not certify worldwide absence, novelty, or publication priority. Those boundaries do not weaken the exact Lean theorem or its source fidelity.
