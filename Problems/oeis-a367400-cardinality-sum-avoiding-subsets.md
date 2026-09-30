---
slug: oeis-a367400-cardinality-sum-avoiding-subsets
bibkey: wu2023a367400
doi: null
url: https://oeis.org/A367400
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/CardinalitySumAvoidingSubsets.result
---

# Cardinality-sum-avoiding subset generating function

## Problem

For n in N, let a(n) count subsets S of {1,...,n} for which no distinct
x,y in S have x+y=|S|. The interval is empty at n=0; a(0)=1.
Equal summands are permitted. Chai Wah Wu's November 21, 2023 conjecture
in OEIS A367400 is

$$ A(X)=\sum_{n\ge0}a(n)X^n
 =\frac{1+X^2-X^3}{1-2X+X^2-2X^3+X^4}. $$

The exact retained statement is

```lean
(1 - 2*PowerSeries.X + PowerSeries.X^2 - 2*PowerSeries.X^3 +
  PowerSeries.X^4 : PowerSeries ℚ) * PowerSeries.mk (fun n => (a n : ℚ)) =
  1 + PowerSeries.X^2 - PowerSeries.X^3
```

The definition of a is the literal filtered powerset cardinality, with
no recurrence, assumed count identity, or assumed bijection. Preregistration: [issue #11453](https://github.com/the-omega-institute/trureturing/issues/11453),
first-tier external conjecture. The corresponding Library note gives the
source and bounded literature scope; neither establishes priority.

## Motivation

The original count has an exact all-degree formal-series description, including
the empty subset and the permitted even midpoint.

## Gap

The checked OEIS source labels the formula a conjecture. The supplied bounded
source scope is A367396, A112575 and Huang arXiv:2501.07463v2; no exact
original-count bridge is supplied from that scope. The counting construction
below gives the bridge for the literal filtered powerset.

## Route

For positive k, the distinct forbidden pairs are {i,k-i} for
1 <= i <= floor((k-1)/2). They are disjoint. A selected pair contributes
one of two orientations, while an even midpoint k/2 has one orientation.
The tail [k,n] is unrestricted. The proof constructs forward and inverse
maps and proves their inverse laws, predicate preservation, range bounds,
and the cardinality constraint.

With

$$P_k(z)=(1+2z)^{\lfloor(k-1)/2\rfloor}
 (1+z)^{[k\text{ even}]},\qquad p_{k,j}=[z^j]P_k(z),$$

the proof derives

$$a(n)=1+\sum_{k=1}^{n}\sum_{j=0}^{\lfloor k/2\rfloor}
 p_{k,j}\binom{n-k+1}{k-j}.$$

The leading one handles the empty subset. P_k is used only for k>=1;
its displayed formula at k=0 is not a model for the lower-block family.

Write U_d=(1-X)^(-d), R=X^3(2-X)U_2, and let F_k be the formal series
of the guarded positive-k summand. Mathlib's negative-binomial identity
and polynomial homogenization give

$$F_{2m+1}=XU_2R^m,\qquad F_{2m+2}=X^2U_3R^m.$$

For each degree n, F_k has zero coefficient when k>n. Since R has zero
constant coefficient, its powers admit the coefficientwise geometric
sum. The proof obtains A=U_1+(XU_2+X^2U_3) sum_m R^m and simplifies it
to the stated identity. X is never inverted, and no analytic convergence
is assumed.

## Falsifier

A counterexample would be a degree at which the original powerset count
violates the displayed formal-series identity. The proof covers every
natural degree, including zero, without empirical coefficient sweeps.

## Evidence

Only the two original-count definitions and one theorem are public.
The two private structures carry the pairing data. Equivalences,
Fintype instances, intermediate series and every helper fact are local
to result. The exact theorem is a scoped Lean result. Repository admission, freezing,
and whole-project CI are separate obligations. Escape registration requires
a source-equivalence bridge, variation, sensitivity, observational dependence,
and current binding evidence. The escape audit is unfinished: the existing
source-family registration's proof obligations compile, but binding assessment
returns `incomplete_closure` under `E8.heartbeats`. Valid current binding evidence
remains required under [issue #11453](https://github.com/the-omega-institute/trureturing/issues/11453).
No Reg mirror is retained.

## Triage

Tier 1 external named OEIS conjecture, preregistration issue #11453.

Proposed admission basis: `open-problem-resolution`, tied to issue #11453.
The complete proof has shape `content`: the original subset encoding,
inverse laws, and orientation/cardinality bridge are constructed here,
not imported as frozen prerequisites. The final rational simplification
alone is normalization. There are no retained companion lemmas.

Utility is `none`: definitions describe mathematical finite families and
the theorem establishes an unbounded symbolic count and formal-series
identity. Its new content is neither a bounded sweep, a checker, a
numerical reduction, nor a certified finite instance.

### What the settlement shows

**Proved:** `D5/S3/Combinatorics/CardinalitySumAvoidingSubsets.result`
establishes the literal original-count law above for every n>=0.
**Inspection of the exact checked proof, not a separate theorem:** the
decisive mechanism is the reversible, cardinality-preserving encoding
into disjoint forbidden-pair choices, the permitted even midpoint and
the free tail. It handles the dependence of the forbidden sum on the
subset's own size. Parity factorization then supplies a common formal
geometric series, justified by finite coefficient support and its
ratio's zero constant term, without a recurrence premise.

**Open extent:** for each fixed integer c, does the count of subsets
S of {1,...,n} with no distinct x,y in S satisfying x+y=|S|+c
(equality in the integers) also have a rational generating function?
Only c=0 is settled here. Extending the method requires verifying the
shifted lower/tail cut and boundary cases when |S|+c<=0 or exceeds n;
analogy does not settle this candidate or admit it as a new target.

**Bounded source consequences:** inspection of
`Library/Combinatorics/wu2023a367400.md`, the A367400/A367396 entries in
`Library/Words/oeis2026triage0910.md`, and this dossier identifies the
quoted generating-function conjecture as the statement settled above.
**Open (unchecked transfers):** extracting the source's fourth-order
recurrence by coefficients and transferring the count to A367396 after
checking the complement identity. The A112575/Huang counting-object
bridge remains **open**. No further result asserted to depend on this
conjecture was identified in those materials; implications beyond that
bounded scope remain **open**.

## ASSUMED-UNVERIFIED

The bounded source and library searches do not establish exhaustive worldwide
novelty, publication priority, or the absence of an independent proof. Final
source review, freezing, repository admission and whole-project checks remain
separate obligations. The Scribe resolution claim requires the declaration's
current frozen membership before emission.
