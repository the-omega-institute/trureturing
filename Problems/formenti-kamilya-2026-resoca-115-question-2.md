---
slug: formenti-kamilya-2026-resoca-115-question-2
bibkey: formentikamilya2026resoca115
doi: 10.4204/EPTCS.445.12
url: https://arxiv.org/abs/2606.13159v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.returns_three_of_returns_nine
  - D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115SquareClosure.result
---

# Formenti–Kamilya Question 2 on RESOCA 115

## Problem

Enrico Formenti and Supreeti Kamilya ask in §3, Question 2, on printed p. 97 (PDF p. 3)

> If $p$ is a period for RESOCA 115, is $p^2$ also a period?

[Versioned author PDF, §3](https://arxiv.org/pdf/2606.13159v1#page=3) · [Proceedings DOI](https://doi.org/10.4204/EPTCS.445.12)

The state $s=(b,c)$ is an ordered pair of past and current Boolean layers on $\mathbb Z$. Equation (1) and Table 1 give $T(b,c)=(c,i\mapsto b_i\oplus(\neg c_i\vee(c_{i-1}\wedge\neg c_{i+1})))$. Let $P(p)$ mean that $p>0$ and there exists a pair $s$ with finite union of initial supports, $T^p s=s$, and $T^q s\ne s$ for each $0<q<p$. Section 2.1 defines finiteness for both layers. The question asks whether $\forall p\in\mathbb N,\ P(p)\Rightarrow P(p^2)$, with an independent existential witness in each occurrence of $P$.

## Motivation

Proposition 1 of the source gives closure under least common multiples. Squaring is the additional closure operation asked about in Question 2. [Versioned author PDF, Proposition 1](https://arxiv.org/pdf/2606.13159v1#page=4)

## Gap

The paper leaves Question 2 open and reports period-nine examples only among nonfinite configurations on printed p. 102. The nine-to-three theorem supplies the universal implication for finite pairs needed to rule out least period nine. The source locators and the original literature screen are recorded in the existing Library note and issue. [Library locator](../Library/Automata/formentikamilya2026resoca115.md#question-2--square-closure) · [Issue #34869](https://github.com/the-omega-institute/trureturing/issues/34869)

## Route

The all-zero pair has empty support, and the successive pairs of uniform layers are $(0,1)$, $(1,0)$ and $(0,0)$. The theorem `zero_period_three` gives the return and its minimality, so $P(3)$ holds. A pair witnessing $P(9)$ would satisfy the finite-support and nine-return hypotheses of `returns_three_of_returns_nine`, and its three-step return would violate leastness. Substituting $p=3$ refutes square closure.

## Falsifier

A finite pair with a nine-step return and no earlier positive return would contradict `returns_three_of_returns_nine`. An alleged different interpretation of period must be checked against the definition and finite-pair quantifier in §3.

## Evidence

The theorem `FormentiKamilyaRule115SquareClosure.result` has literal Lean type `¬ claim` and refutes the full quantified proposition at three. Its axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. [Lean source](../D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115SquareClosure.lean)

The forecasts for the stated event and the mathematical settlement are recorded on issue #34869. [Forecasts](https://github.com/the-omega-institute/trureturing/issues/34869#issuecomment-7220080110) · [Settlement](https://github.com/the-omega-institute/trureturing/issues/34869#issuecomment-7221908984)

## Triage

The external open-problem resolution is refuted by `D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115SquareClosure.result`. The counterexample is a certified instance at $p=3$. The result concerns the set of positive least periods of finite initial pairs on the full integer line.

## ASSUMED-UNVERIFIED

The literature screen in issue #34869 is incomplete. Worldwide priority remains unverified.
