---
slug: formenti-kamilya-2026-resoca-115-question-1
bibkey: formentikamilya2026resoca115
doi: 10.4204/EPTCS.445.12
url: https://arxiv.org/abs/2606.13159v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.returns_three_of_returns_nine
  - D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.result
---

# Formenti–Kamilya Question 1 on RESOCA 115

## Problem

Enrico Formenti and Supreeti Kamilya, *The Curious Case of Reversible Elementary Second Order Cellular Automaton 115*, GASCom 2026, EPTCS 445, pp. 95–103, Question 1 on printed p. 97 (PDF p. 3). [Proceedings DOI](https://doi.org/10.4204/EPTCS.445.12) · [arXiv v1](https://arxiv.org/abs/2606.13159v1)

> For RESOCA 115, in the context of finite configurations, are all multiple of 3 periods?

For $s=(b,c)$ with Boolean layers on $\mathbb Z$, Equation (1) on printed p. 96 and Table 1 on p. 97 give the global reversible update $T(b,c)=(c,i\mapsto b_i\oplus(\neg c_i\vee(c_{i-1}\wedge\neg c_{i+1})))$. Here $b$ is the past layer and $c$ is the current layer. Require the union of the supports of both initial layers to be finite. The elementary local rule contributes to the update of the current layer. The lattice is the full integer line, with no periodic spatial boundary. For every positive multiple $p$ of three, the proposition asserts a state $s$ with that finite support, $T^p s=s$, and $T^q s\ne s$ for every $0<q<p$. This is the least-period question from issue #34754.

## Motivation

The theorem `D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.returns_three_of_returns_nine` proves that for every such finite state a nine-step return entails a three-step return. The theorem `D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.result` consumes this fact at $p=9$.

## Gap

The source states Question 1 explicitly. The literature note records the publication date, v1 submission date and printed page locators. [Library note](../Library/Automata/formentikamilya2026resoca115.md)

## Route

Encode cyclic time columns of length nine as masks. The checked certificate has 31 candidate masks, 40 forward pairs, 52 forward edges, 3 returning pairs and 5 returning edges. Finite propagation from both finite layers supplies the repeating background on both integer tails. At time $n$, agreement holds outside the initial support bound enlarged by $n$. Forward closure from the left and predecessor closure from the right constrain every adjacent pair along arbitrary finite integer segments. The surviving masks are three-shift invariant. The time-nine return identifies the wraparound of both layers, so the entire state returns at time three. The finite bound is in time-period column graphs and leaves spatial width arbitrary.

## Falsifier

A state with finite union support and least period nine would satisfy the hypotheses of `returns_three_of_returns_nine` and would contradict its three-step equality.

## Evidence

The author result is kernel checked under Lean 4.35.0 and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679` with only `propext`, `Classical.choice` and `Quot.sound`. The literal `Set.Finite` predicate and least-period inequalities occur in `claim`. `result : ¬ claim` discharges the exact negation at nine. The scratch module's canonical source is `D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.lean`.

## Triage

Issue #34754. Candidate admission basis `open-problem-resolution` with `bounded-enumeration`, `basis=refutes`, and result selector `D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.result`. Stage B attaches one typed Refuted resolution to `result` after the canonical writer freeze. No freeze identity has been established in scratch. The result excludes least period nine. Period eighteen and a classification of all periods remain outside the result.

## ASSUMED-UNVERIFIED

The versioned paper establishes the historical wording. Independent solutions and worldwide priority were outside this source verification. Canonical resolution depends on admission of this dossier and validation of the designated declaration against the writer's current frozen state.
