---
slug: hanna-a382319-a382318-lambert-cube-mod-three
bibkey: hanna2025a382319
doi: null
url: https://oeis.org/A382319
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaLambertCubeModThreeConverse.result
---

# Hanna's A382319 congruence modulo three

## Problem

Paul D. Hanna's [OEIS A382319](https://oeis.org/A382319), Comments (unpaginated), states:

> Conjecture: a(n) == A382318(3*n) (mod 3) for n >= 0.

The source equations are $A=X+L(A)^3$ and $B=X(1-X)^{-1}+L(B^3)$,
where $L(F)=\sum_{k\ge1}F(X^k)$ and both series have zero constant term.
At degree $m$, $L(F)$ has coefficient $\sum_{1\le k\le m,\ k\mid m}[X^{m/k}]F$.
The empty degree-zero sum is zero. The cube in the second equation is taken
before Lambert summation. The source is recorded in the
[Library note](../Library/RecurrenceComposition/hanna2025a382319.md).
Preregistration: [#18862](https://github.com/the-omega-institute/trureturing/issues/18862).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Two generating equations, with offset one | `IsA382318 A`, `IsA382319 B` in `HannaLambertCubeModThree` | Literal rational equations and zero constant coefficients. |
| Infinite substitution sum | `lambertSum` | Positive-divisor coefficient sum; natural-number division. |
| Sequence values | `PowerSeries.coeff` | Integer witnesses are cast into rational coefficient equalities. |
| Nonnegative index | Natural-number binder | Includes zero. |
| Reciprocal congruence | Universal conjunct of `claim` | $b(n)\equiv a(3n)\pmod3$. |
| Existence | Existential conjunct of `claim` | Additional conclusion; no restriction of the source's solution class. |
| Every solution pair | Universal quantifiers and the two predicate hypotheses | No selected solution replaces the source's generating functions. |

The congruence is $b(n)\equiv a(3n)\pmod3$ for every natural $n$, including zero. No source clause is dropped. The complete proposition is displayed
at both `claim` and `result` in the Blueprint.

## Motivation

The congruence links two implicit generating functions rather than two
independently chosen coefficient lists. The coefficientwise Lambert relation
and the identity $A=X+B^3$ identify the common realization needed for Frobenius.

## Gap

The source and literature screen recorded in #18862 found no published proof
or refutation in the entry, its links, the searched OEIS-proof papers and formal
conjecture catalogues. Completeness and continued external open status are
`ASSUMED-UNVERIFIED`. The delivered result is a settlement under the literal
preregistered rational power-series conventions.

## Route

The first module constructs the integral fixed point of $F\mapsto X+L(F)^3$
by coefficient stabilization. The contraction of agreement below a degree
gives existence and uniqueness. Compatibility with coefficient ring maps
identifies every rational solution with the integral one. Linearity of $L$
and $L(X)=X(1-X)^{-1}$ give $B=L(A)$ and $A=X+B^3$.
Cubic Frobenius modulo three then gives $A\equiv X+B(X^3)$.
The proof uses coefficient agreement `Agree` and `agree_cube` from
`CubicFifteenSubstitutionParity`, and `cube_congr_subst_three` from
`CubicTernarySubstitutionParity`. These are actual elaborated dependencies.
The converse module applies `HannaLambertCubeModThree.result` and `Int.ModEq.symm`.

## Falsifier

A solution pair with a nonintegral relevant coefficient or a violated residue
would contradict `result`. Interpreting the infinite sum with a nonzero constant
coefficient would change the source-to-formalization bridge and is excluded by
the source offsets and the explicit predicate hypotheses.

## Evidence

`D5.S1.Recurrence.Invariants.HannaLambertCubeModThreeConverse.result` proves `claim`.
The two delivered modules carry admission bases
`open-problem-resolution (#18861; Proved)` and
`open-problem-resolution (#18862; Proved)` respectively.
Their axiom closures are contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The four-slot escape audit is unfinished for both public results:
[issue #19096](https://github.com/the-omega-institute/trureturing/issues/19096).
The source propositions mix solution existence, universal solution-pair
hypotheses and integer witnesses. No compiled registration reconstructing this
whole telescope, observational dependence, variation and sensitivity is delivered.
No `declared_validated` registration is claimed.

### Experiment

[Published checker and data](https://github.com/the-omega-institute/trureturing-experiments/tree/7b61b379bca979d9231306df7e0b20924bcc3491/docs/reports/oeis-a382318-a382319-a382124-a382125-hanna-frobenius-mod3).
Command: `python3 check.py 300`, run in that directory; exit 0, `RESULT PASS`.
The pinned `check.py` SHA-256 is
`319ee58b884641c875833eb3e830906af72d593ab73e1d6b0da6ff155cd352f3`.
The checked A382318 and A382319 coefficients match their b-files through
index 300; $L(A)=B$, $A=X+B^3$ and $B^3\equiv B(X^3)\pmod3$ hold
through degree 300. The paired congruence is checked for $3n\le300$;
the two zero residues are checked for $n\ge1$ and $3n+2\le300$.
These finite computations do not establish an unbounded statement.

## Triage

| Item | Status | Evidence |
| --- | --- | --- |
| A382318 congruences | Proved, kernel-checked | `HannaLambertCubeModThree.result`. |
| A382319 converse congruence | Proved, kernel-checked | `HannaLambertCubeModThreeConverse.result`. |
| Finite coefficient and residue check | Computed | The experiment entry above; exactly its stated ranges. |
| General prime-exponent extension | Proved in prose below; Lean formalization open | Division-free contraction and prime Frobenius, as detailed below. |
| Asymptotic formula | Open | No asymptotic estimate is asserted or formalized. |
| Literature completeness | Open (`ASSUMED-UNVERIFIED`) | The scope of the screen in #18862. |
| Escape registration | Open | #19096; no registration evidence is claimed. |

### What the settlement shows

**Proved, kernel-checked.** `HannaLambertCubeModThreeConverse.result` gives the full
conjecture with existence and universal solution-pair quantification. The
first module's private `solution_fixed`, `fixed_unique`, `solution_link`
and `integral_pair` establish the fixed-point mechanism, uniqueness,
$B=L(A)$, $A=X+B^3$, and integrality used in this conclusion.
These helpers are supporting proof facts, not additional public settlements.

**Proved in prose; general-prime Lean formalization open.** For a prime
$p$, replace the cube by the $p$th power. Every $L(F)$ has zero constant
coefficient. If $F$ and $G$ agree below degree $d$, the factorization of
$L(F)^p-L(G)^p$ shows agreement below $d+p-1$: one factor agrees below
$d$, and each of the remaining $p-1$ factors has order at least one.
Since $p\ge2$, iteration stabilizes each coefficient, giving a unique
fixed point over $\mathbb Z$ and then over $\mathbb Q$. Linearity of $L$
gives a solution $B=L(A)$ of $B=X(1-X)^{-1}+L(B^p)$.
Conversely, that equation gives $L(X+B^p)=B$, so $X+B^p$ is a solution
of the first equation. Its uniqueness makes this correspondence unique.
Over $\mathbb F_p$, Frobenius gives $B(X)^p=B(X^p)$, hence
$a(pn)\equiv b(n)\pmod p$ for all $n\ge0$, and
$a(pn+r)\equiv0\pmod p$ when $n\ge1$ and $0<r<p$.
This is a mathematical extension of the mechanism, not a Lean theorem of
these modules and not an assertion about the experiment's tested scope.

**Explanation.** The exceptional term $X$ accounts for $a(1)=1$; the
zero-residue assertion in the source therefore starts at $n=1$.
The source's reciprocal congruence is settled by symmetry in #18862.
No other source result depending on the conjecture was identified in the
recorded screen. The entry's asymptotic formula remains open here, since
coefficient residues do not supply an asymptotic estimate.

## ASSUMED-UNVERIFIED

The literature screen is not exhaustive. Continued external open status,
completeness of the search, and the source-to-formalization interpretation
of the OEIS infinite sums are not kernel assertions. The general-prime
extension above is a prose proof, with its Lean formalization open.
