---
slug: notik-singer-chamber
bibkey: notik2026singergolomb
doi: 10.48550/arXiv.2611.22656
url: https://arxiv.org/abs/2611.22656v1
triage: theorem
motivation_gids:
  - D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.result
---

# Singer rulers are the unique shortest points of their chambers

## Problem

Esther Notik states the following conjecture in §7 of [arXiv:2611.22656v1](https://arxiv.org/pdf/2611.22656v1#page=7).

> For every prime power m, every Singer ruler is the only shortest point of its chamber.

For every prime power $m$, take a Singer perfect difference set $D$ modulo $N=m^2+m+1$, multiply it by any unit modulo $N$, and cut at any largest cyclic gap $G$. Translate the marks so the first is zero. In §2 the order chamber consists of real rulers with first mark zero, the same order of labelled ordinary positive distances, and each distance and each difference between distinct ordered distances at least one in the indicated direction. The objective is the last mark. The conjecture is the assertion preregistered in [#31476](https://github.com/the-omega-institute/trureturing/issues/31476).

## Motivation

The paper reports exact certificates for 24,450 distinct Singer rulers with prime-power order at most 103. A single argument for all sizes gives the chamber minimum and its unique minimizer for the full family.

## Gap

The arXiv version record lists v1 with the conjecture. The data and certificate archive gives the completed range through order 103 and records a computation that stopped during order 107. The bounded arXiv title and Singer chamber search recorded for the source did not find a general proof. [arXiv version record](https://arxiv.org/abs/2611.22656) · [Data and certificate archive](https://doi.org/10.5281/zenodo.24309145)

## Route

The normalized integer ruler has length $L=N-G$. Every residue $d$ with $1\le d<G$ occurs as an oriented difference. If that difference wraps in the cut order, the underlying ordinary distance is $N-d>L$, which is impossible. Thus each integer $1,\ldots,G-1$ occurs as an ordinary distance.

A retained adjacent gap has length $g\le G$. Its chamber preserves the order of the labelled distances realizing $1,\ldots,g-1$ and the gap of length $g$. The smallest distance and successive differences along this list are at least one for any real point in the chamber. Induction bounds the corresponding real gap below by $g$. The ordinary integer distances of the original ruler are positive and pairwise distinct by the perfect difference property, so the original point is feasible. Summing the gap bounds gives the minimum and equality forces each gap to agree. Anchoring the first mark fixes the entire ruler.

## Falsifier

A refutation would exhibit a cyclic Singer ruler cut at a largest gap and a different normalized real ruler in the same chamber with length at most its length.

## Evidence

Lean checks that for any $m>0$ and strictly increasing natural marks starting at zero, with a positive cut gap $G$ bounding all retained gaps and the cyclic perfect difference property modulo $x_{\mathrm{last}}+G$, the ordinary distances are distinct, the real cast is feasible, and every point in the chamber of length at most $x_{\mathrm{last}}$ agrees with it at every mark. The cyclic perfect difference property is a hypothesis of `D5/S3/Geometry/FiniteGeometry/NotikSingerChamber.result`.

The classical Singer construction supplies $m+1$ residues with the perfect difference property for every prime power $m$. A unit permutes the residues and sends each ordered difference to its unit multiple. Translating the first mark after any largest gap to zero preserves every modular difference. Sorting the representatives in $[0,N)$ gives strict increase, $G=N-x_{\mathrm{last}}>0$, and the required adjacent-gap bound. This specialization establishes the §7 claim for all prime powers, unit multipliers and largest-gap cuts. [Singer (1938)](../Library/FiniteGeometry/singer1938projective.md) · [Notik, §7](https://arxiv.org/pdf/2611.22656v1#page=6)

Pass from normalized marks to consecutive gaps by subtraction and recover the marks by cumulative sums. Each labelled distance becomes the corresponding interval sum. The distinct reference distances select the signs of the comparison rows in §2, yielding the inequalities in `Chamber`. The length is the sum of the gaps, which equals the last mark because the first is zero.

## Triage

### What the settlement shows

Chamber uniqueness is proved by the coordinatewise lower bound on all retained gaps. The argument applies to every largest-gap cut of a cyclic perfect difference set and gives a symbolic chamber certificate. Write $a_i$ for the integer gaps, $A=\max_i a_i$, and $v_d$ for the interval row of the ordinary distance $d$, for $1\le d\le A$. These distances exist because all $d<G$ occur and $A$ itself is a retained gap. The tight rows $r_1=v_1$ and $r_d=v_d-v_{d-1}$ for $2\le d\le A$ telescope to the coordinate row $v_{a_i}$ of gap $i$. Giving row $r_d$ weight $|\{i:a_i\ge d\}|$ yields the all-ones objective with total weight $\sum_i a_i$. The same identities show that the positively weighted rows span the gap coordinates.

The separate §10 question classifying the global shortest real rulers at 8, 9 and 10 marks has a reported Lean proof that the minimizers are exactly the optimal integer rulers, at lengths 34, 44 and 55, respectively. Its canonical freeze and delivery are tracked separately. [#31427 proof report](https://github.com/the-omega-institute/trureturing/issues/31427#issuecomment-6975703095) The certificate concerns the chamber of a largest-gap cut. The source’s other-gap computations include cases with shorter or tied rulers.

## ASSUMED-UNVERIFIED

Literature completeness and priority beyond the bounded search are unverified. The paper and companion archive attest the finite certificate counts.
