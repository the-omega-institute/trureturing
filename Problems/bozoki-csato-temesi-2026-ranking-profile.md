---
slug: bozoki-csato-temesi-2026-ranking-profile
bibkey: bozokicsatotemesi2026dice
doi: 10.48550/arXiv.2611.23308
url: https://arxiv.org/abs/2611.23308v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Dice/RankingProfileRealization.problem_five
---

# Bozóki–Csató–Temesi Problem 5 on complete ranking profiles

## Problem

For every nonnegative real vector $v=(v_1,\ldots,v_6)$ summing to one, Problem 5 asks when there exist three independent real-valued random variables whose six strict ordering probabilities are exactly $v$. The order in Equation (7) is $XYZ,XZY,YXZ,YZX,ZXY,ZYX$, each word read from largest to smallest. The full simplex includes points with zero coordinates. [arXiv:2611.23308v1, §5, printed p. 6](https://arxiv.org/pdf/2611.23308v1#page=6)

## Motivation

Pairwise comparison probabilities are sums of the six strict-order coordinates. Problem 5 seeks a criterion for the full joint ranking profile, including boundary profiles.

## Gap

The paper gives a pairwise criterion in Theorem 6 and treats a specified branch with fixed interlaced supports in Theorem 12. The source question ranges over arbitrary independent real laws and all simplex profiles. The preregistration records the scoped literature checks and the unchecked coverage of Suck's 2002 text. [Issue #34280](https://github.com/the-omega-institute/trureturing/issues/34280)

## Route

For $v$ in the simplex, introduce three weight vectors $p_A$ on $\{1,\ldots,15\}$ for $A=X,Y,Z$. Each vector is nonnegative, sums to one and has at most five positive entries. The exact criterion requires the six equations

$$
v_{ABC}=\sum_{15\ge i>j>k\ge 1}p_A(i)p_B(j)p_C(k)
\qquad(ABC\in\{XYZ,XZY,YXZ,YZX,ZXY,ZYX\}).
$$

A real realization has distinct values almost surely because the six strict events are disjoint and exhaust mass one. Clamped floor quantizers with separate residue classes give independent finite variables with disjoint ranges and convergent ranking probabilities. Holding two finite marginal laws fixed gives two complementary block sums of three coordinates each. These fix two coordinates in terms of the other four, so Carathéodory reduces the remaining marginal to five points from its existing support. Repeating for the three marginals preserves disjointness and every coordinate. Relabel the combined ordered support in at most fifteen labels. The sparse simplex is a finite union of compact faces, and the continuous cubic image is closed. The reverse direction uses the product of the three finite marginal laws.

## Falsifier

A simplex profile admitting an independent real realization but failing the weight constraints and six cubic equations, or passing them without an independent real realization, would refute the criterion. The proof depends on strict event convergence, preservation of every coordinate during compression, closedness of the capped image, and exact product masses in the reverse construction.

## Evidence

The theorem `D5/S3/Combinatorics/Dice/RankingProfileRealization.problem_five` states necessity on arbitrary measurable probability spaces and sufficiency on triples of finite labels with real-valued coordinate maps. Lean uses zero-based labels with the same strict order. The probability Blueprint describes the rank order, real profile and resolution theorem. The finite grid Blueprint describes the cubic test, support compression and closedness used by the theorem.

## Triage

Tier 1, theorem.

### What the settlement shows

The theorem `D5/S3/Combinatorics/Dice/RankingProfileRealization.problem_five` proves the full criterion and answers the general support-size question in §7 with a uniform upper bound of fifteen. The fixed-pair block sums drive the reduction from six profile coordinates to four. Sharpness remains open in this work.

A separate mathematical strengthening gives at most fourteen labels with caps $4,5,5$, where any one prescribed role may take the cap of four. Smooth the other two marginals in disjoint intervals that preserve the original comparisons. The six conditional ranking probabilities then vary continuously with the designated value in an affine subspace of dimension at most four. Path compression reduces its convex representation to four points. Quantization, compression of the other marginals and closedness yield the strengthened criterion. The path-compression sublemma has been checked separately in Lean. The full fourteen-label argument remains outside the formal claim here. [Mathematical proof in issue #34280](https://github.com/the-omega-institute/trureturing/issues/34280)

## ASSUMED-UNVERIFIED

Four-slot registration is open for `problem_five` and for the finite grid theorems `isClosed_finiteTest15` and `profile_mem_finiteTest15`. The enrolled `existentialWitnessRealization` can read acceptance of a chosen triple of weight vectors at a fixed input. Its law only asserts existence of an accepted state. The compression theorem also quantifies over finite ordered carriers and all three input weights, subject to normalization and support disjointness. A source binding through `DependentFamily.realize` would need a readout tied to the cubic profile in every admissible input fiber. For closedness, it would need to recover the topology of the real profile space and its limit-closure law from the exact `IsClosed` statement. Both bindings still need exact source reconstruction, a law equivalence, and proofs of interventions, sensitivity and actual observational dependence. [Original result registration gap #34292](https://github.com/the-omega-institute/trureturing/issues/34292)

The full fourteen-label criterion has no end-to-end Lean proof in this delivery. The scoped literature checks establish no global priority claim.
