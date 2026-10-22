---
slug: oeis-a378258-hanna-square-root-parity
bibkey: hanna2024a378258
doi: null
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaA378258SquareRootParity.result
url: https://oeis.org/A378258
---

## Problem

Paul D. Hanna's OEIS A378258 Name states: "G.f. satisfies A(x) = B(x) + 5*A(x)^2 where B(A(x) - A(x)^2) = x." Its Comments state: "Conjecture: a(n) is odd iff n is a power of 2."

The normalized rational series has constant coefficient zero and linear coefficient one, with offset one. The binding statement of [#18825](https://github.com/the-omega-institute/trureturing/issues/18825) asserts existence, integrality and dyadic parity for every normalized solution and every $n\ge1$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $A=B+5A^2$ | `IsGF` existentially quantifies the rational series $B$ and includes this equality | Literal source equation. |
| $B(A-A^2)=x$ | `IsGF` includes `PowerSeries.subst (A - A ^ 2) B = X` | The inner series is the first argument of substitution. |
| Offset one and $a(1)=1$ | `IsGF` requires constant coefficient zero and linear coefficient one | Source normalization. |
| A generating function exists | The first conjunct of `claim` is existence of an `IsGF` solution | Prevents vacuity. |
| Integer sequence and parity conjecture | `claim` provides an integer representative of each coefficient, with oddness equivalent to $n=2^k$ for some natural $k$ | Every natural degree at least one; no finite cutoff. |
| Every normalized solution | Universal quantification over rational $A$ satisfying `IsGF` | Uniqueness identifies all such solutions; no extra assumption. |

## Motivation

The parity assertion depends on an integral construction of the generating function. The compositional square of the auxiliary series equals $5X-4K$, where $K=X+K^2$ is the normalized Catalan series. An integral square root congruent to $X$ modulo two transfers the Catalan coefficient support to the source solution.

## Gap

The literature screen in #18825 found the entry's formula (6), $B\circ B=5X-4K$, without the integral square-root argument. No proof was found in the entry, its revisions, the Catalan cross-references or the formal-conjecture catalogues named in that issue. Literature completeness and continued external open status are `ASSUMED-UNVERIFIED`. This is settlement of an explicitly published named conjecture; no originality of the lifting method is asserted.

## Route

For $H\in X^2\mathbb Z[[X]]$, correct successive coefficients of a series beginning with $X$. If its displacement from $X$ is even, its compositional residual is divisible by four. Dividing the next residual coefficient by two therefore gives an even correction. The triangular substitution identity cancels that residual coefficient while preserving every preceding coefficient. Compatible approximants define an integral series $S$ with $S\circ S=X+4H$ and $S\equiv X\pmod2$.

Take $H=X-K$ and write $J$ for the compositional inverse of $S$. Set $A=K\circ J$. The Catalan equation implies $A-A^2=J$ and $A-5A^2=S$, establishing both source equations. For any normalized rational solution, the auxiliary series has the same compositional square as $S$. `HannaHalfIterateCubicModThree.half_unique` identifies these roots, and hence the solution. Reduction modulo two gives $\overline A=\overline K$; `CatalanCompositionSquareParity.binary_catalan` supplies the dyadic support.

The consumed coefficient owners are `CompositionalSquareDyadicDenominators.agree_subst`, `composition_top`, `C_dvd_iff_coeff`, `residual_four` and `coeff_subst_sum`. Mathlib supplies formal substitution, coefficient maps and compositional inverse identities.

## Falsifier

A normalized source solution with a nonintegral coefficient or with parity different from the dyadic support would contradict `result`. Degree zero is outside the source offset. The conclusion is universal in degree, rather than an inference from a finite coefficient test.

## Evidence

`D5.S1.Recurrence.Invariants.HannaA378258SquareRootParity.result` proves the exact public `claim`. The admission basis is `open-problem-resolution (#18825; Proved)` and there is no anchor atom. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The four-slot escape audit is unfinished under [#19870](https://github.com/the-omega-institute/trureturing/issues/19870). The targets are `HannaA378258SquareRootParity.result`, `HannaHalfIterateCubicModThree.half_unique` and `CompositionalSquareDyadicDenominators.coeff_subst_sum`. No Reg mirror is delivered: complete source reconstruction, an enrolled readout, actual-positive law, variation, sensitivity and observational-dependence evidence remain missing. No `declared_validated` status is asserted.

### Experiment

[Published checker and data](https://github.com/the-omega-institute/trureturing-experiments/tree/9dfe5bdc210cac281a148e7180239ddb21b0b34b/docs/reports/oeis-hanna-parity-family-research).
Command: `python3 check.py`, run in that directory; exit 0, `RESULT PASS`. The script SHA-256 is `ec87bb1637d6a946d4e5fb43f078bc623ce327257ef53b9305c05c564ca154b5`.
For A378258 the first twelve terms match the entry, all tested coefficients are integral, and the parity assertion holds for $1\le n\le40$. This is finite experimental evidence; `result` supplies the unbounded conclusion.

## Triage

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| The normalized source system has an integral solution with the stated parity | Proved | Kernel-checked `HannaA378258SquareRootParity.result`, every $n\ge1$. |
| Every integral target $X+4H$ with $X^2\mid H$ has a normalized integral compositional square root congruent to $X$ modulo two | Proved | Kernel-checked private `IntegralSquareRoot.root_spec`, consumed by `square_root_spec`. |
| Replacing five by $1+4t$, for integral $t$, leads to the target $X+4t(X-K)$ and a candidate general parity family | Open candidate | Algebraic route below; no parameter-family Lean settlement is delivered. |
| The separate conjecture excluding residues one and five modulo six for $n>1$ | Open | Outside `claim`; neither the parity proof nor the finite experiment entry establishes it. |
| The assertion concerning the first negative term | Open | Outside `claim`; no sign theorem is delivered. |
| Twelve source terms, integrality and dyadic parity through degree forty | Computed | The pinned experiment and exact tested scope above. |
| Source formula (6) and source consequences | Proved in prose as an identity; parity kernel-checked | The derivation below connects the formula to the integral construction. No further source theorem depending on the conjecture is identified by #18825. |
| Literature status | Literature reading; completeness `ASSUMED-UNVERIFIED` | The screen recorded in #18825. |
| Escape registration | Open | #19870 and the missing evidence above. |

### What the settlement shows

**Proved, kernel-checked.** `IntegralSquareRoot.root_spec` establishes the general integral lifting mechanism for every $H$ of order at least two. The even corrections and stable coefficients, rather than finite numerical agreement, produce the integral square root. The private `solution_unique` identifies every normalized rational source solution, and `result` proves integrality and dyadic parity.

**Proved in prose.** The Catalan identity $K-K^2=X$ gives $K-5K^2=5X-4K$. Composing $A-5A^2=B$ with $B$ and using $A\circ B=K$ therefore yields the source formula $B\circ B=5X-4K$. The integral square-root construction supplies the integrality step this identity alone does not establish.

**Open candidate.** With $c=1+4t$, the same algebra gives $K-cK^2=X+4t(X-K)$. Since $X^2\mid X-K$, the integral lifting mechanism applies to this target. This identifies a candidate route to a parameter-family parity theorem; its full source-system correspondence and Lean settlement are not additional conclusions of `result`.

**Open.** Parity does not decide the source's separate modulo-six exclusion or the first negative term. Those remain distinct questions. The quoted parity conjecture becomes a theorem under the stated normalization; no additional source dependency is asserted.

## ASSUMED-UNVERIFIED

The external literature screen is incomplete. The statement's identification with the OEIS entry uses the quoted source and normalization in #18825. The four-slot audit remains unfinished under #19870. The parameter-family settlement, modulo-six assertion and first-negative-term assertion remain outside the proved public claim.
