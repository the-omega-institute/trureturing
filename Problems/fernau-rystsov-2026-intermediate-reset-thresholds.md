---
slug: fernau-rystsov-2026-intermediate-reset-thresholds
bibkey: fernau2026shortest
doi: 10.48550/arXiv.2611.09136
url: https://arxiv.org/abs/2611.09136v1
triage: theorem
motivation_gids:
  - D5/S0/Automata/FernauRystsovIntermediateReset.result
---

# Every intermediate reset threshold occurs in a DFA product

## Problem

The second bullet of §7, printed p. 19, asks the following. [arXiv:2611.09136v1, §7](https://arxiv.org/pdf/2611.09136v1#page=19)

> Can we show that each “intermediate number” between the lower and upper bound of Proposition 7 can be attained?

For every triple of natural numbers $r,s,m$ with $\max(r,s)\le m\le r+s$, the question is whether there are finite deterministic automata with total transitions, nonempty state sets and one shared alphabet whose factor reset thresholds are $r$ and $s$ and whose synchronous direct product has threshold $m$. The threshold of a synchronizable automaton is the minimum length of a word whose image of the full state set is a singleton. The minimum ranges over all finite words, including the empty word. [Definitions, §2](https://arxiv.org/pdf/2611.09136v1#page=3) · [Scope, issue #34708](https://github.com/the-omega-institute/trureturing/issues/34708)

## Motivation

Proposition 7 bounds the product threshold below by the larger factor threshold and above by their sum. The lower bound follows by projection onto both factors. The upper bound follows by concatenating a reset of each factor. [Lemmas 5–6 and Proposition 7, §3](https://arxiv.org/pdf/2611.09136v1#page=5)

## Gap

The two inequalities constrain each synchronizable direct product. Attainment asks for a pair of factors for every integer in the resulting closed interval with the factor thresholds fixed.

## Route

Use the state sets $\{0,\ldots,r\}$ and $\{0,\ldots,s\}$ and the alphabet $\mathrm{Bool}$ with $a=\mathrm{false}$ and $b=\mathrm{true}$. Put $t=r+s-m$. The interval gives $t\le r$ and $t\le s$. In the first chain, $a$ advances a state by one up to $r$, and $b$ advances a state by one below $t$ and fixes it at or above $t$. In the second chain, $a$ fixes each state and $b$ advances a state by one up to $s$.

The words $a^r$ and $b^s$ reset the factors. Both top states are fixed by both letters and the respective coordinates increase by at most one per letter, so these words are shortest. In the product, $b^s$ takes every first coordinate to at least $t$ and every second coordinate to $s$. Then $a^{r-t}$ reaches $(r,s)$ from every pair. The word $b^sa^{r-t}$ has length $m$.

Every product reset must take $(0,0)$ to the fixed pair $(r,s)$. Along any word the potential $\max(i-t,0)+j$ increases by at most one per letter. Its increase between those pairs is $r-t+s=m$, so no shorter product reset exists. [Construction and settlement, issue #34708](https://github.com/the-omega-institute/trureturing/issues/34708#issuecomment-7208766205)

## Falsifier

A shorter reset of either specified factor or of the specified product would contradict its fixed-top lower bound. Failure of one of the three explicit reset words on any initial state would contradict its witness calculation. At $m=\max(r,s)$ the construction uses $t=\min(r,s)$, and at $m=r+s$ it uses $t=0$. When a factor threshold is zero its chain is a singleton, the empty word is a shortest reset of that factor, and $m$ equals the other threshold.

## Evidence

`D5/S0/Automata/FernauRystsovIntermediateReset.result` proves interval attainment with `Fin (r + 1)` and `Fin (s + 1)` as the state sets and `DFA.inter` as the synchronous product. Each threshold includes a singleton-image witness and a lower bound quantified over every resetting word. The declaration has statement identity `sha256:fc45f74f1beaa9363b254b0d1ef3f90f04ac4ba86b2319f22276c8dbd07a1fa4` and uses `Classical.choice`, `Quot.sound`, and `propext`.

## Triage

The Tier 1 question is proved for the full interval. Proposition 7 supplies necessity, so the interval gives precisely the possible finite thresholds with the prescribed factor thresholds. The proof uses a shared two-letter alphabet throughout.

## ASSUMED-UNVERIFIED

The bounded literature screen in issue #34708 found the interval bounds and the unary case at the lower endpoint. The earlier shortest-prefix counterexample also realizes the single triple $(2,3,4)$. Worldwide priority and completeness of the literature search are unverified. [Issue #34708](https://github.com/the-omega-institute/trureturing/issues/34708) · [Earlier result](https://github.com/the-omega-institute/trureturing/pull/33863)
