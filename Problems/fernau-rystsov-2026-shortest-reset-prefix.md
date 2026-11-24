---
slug: fernau-rystsov-2026-shortest-reset-prefix
bibkey: fernau2026shortest
doi: 10.48550/arXiv.2611.09136
url: https://arxiv.org/abs/2611.09136v1
triage: theorem
motivation_gids:
  - D5/S0/Automata/FernauRystsovShortestResetPrefix.result
---

# A shortest first-factor reset can miss the product optimum

## Problem

The fourth bullet of §7, printed p. 19, asks:

> The upper-bound construction of Proposition 7 was somehow naive, as it assumed that the ‘work’ that w₁ did concerning the second automaton was completely ignored. Can we always rely on first synchronizing A₁ optimally (possibly we have to pick a ‘most suitable’ shortest synchronizing word for A₁) and then solving a ‘subset synchronization’ problem for A₂ ?

The scope is the optimal-length reading fixed by [issue #33847](https://github.com/the-omega-institute/trureturing/issues/33847). The paper's Lemma 6 proves feasibility by concatenating a reset of each factor. Proposition 7 still bounds the product threshold between the maximum and the sum of the factor thresholds. [Question, arXiv:2611.09136v1, §7](https://arxiv.org/pdf/2611.09136v1#page=19) · [Lemmas 5–6 and Proposition 7](https://arxiv.org/pdf/2611.09136v1#page=5)

For every ordered pair of total DFAs over an arbitrary common nonempty finite alphabet, with both state sets nonempty and finite, assume each factor admits a reset. The assertion is that there are words $u,v$ such that $u$ is a shortest reset of the first factor, $v$ is a shortest reset of the second-factor image after $u$, and $uv$ is a globally shortest reset of the entire shared-letter direct product. A reset takes the specified set to a singleton. Each minimum is over all finite words, including the empty word. The initial and accepting fields of the DFAs play no role.

## Motivation

A shortest first-factor reset can already compress the second factor. Choosing among tied shortest first-factor words and optimizing the remaining work could reduce the concatenation bound for a given pair.

## Gap

The maximum and sum bounds on the product threshold do not decide whether any unrestricted optimum begins with a shortest first-factor reset.

## Route

For a first-factor reset $u$, appending $v$ resets the full product exactly when $v$ collapses the second-factor image after $u$. If $uv$ is globally shortest, every other reset of that image has length at least $|v|$. This gives the equivalence to a globally shortest product reset with a shortest first-factor prefix. Bijections with finite ordinal sets preserve word evaluation, lengths, and concatenation.

## Falsifier

Use the alphabet $\{a,b\}$ and state sets $\{0,1,2\}$ and $\{0,1,2,3\}$. Each tuple lists the images of the states in increasing order.

| Factor | Letter $a$ | Letter $b$ |
| --- | --- | --- |
| First | $(0,0,1)$ | $(1,2,0)$ |
| Second | $(1,1,2,0)$ | $(0,2,3,0)$ |

The complete reset lists through length four are:

| Length | Words | First factor | Second factor | Product |
| --- | ---: | --- | --- | --- |
| 0 | 1 | ∅ | ∅ | ∅ |
| 1 | 2 | ∅ | ∅ | ∅ |
| 2 | 4 | aa | ∅ | ∅ |
| 3 | 8 | aaa, aab, baa | bbb | ∅ |
| 4 | 16 | aaaa, aaab, aaba, aabb, abaa, baaa, baab, bbaa | abbb, bbaa, bbba, bbbb | bbaa |

The unique shortest resets are `aa`, `bbb`, and `bbaa`, of lengths 2, 3, and 4 respectively. The first letter of `bbaa` excludes the only shortest first-factor prefix. The second-factor image after `aa` is $\{1,2\}$, and its unique shortest reset is `bbb`. Thus the shortest completion of `aa` has length 5.

## Evidence

`D5/S0/Automata/FernauRystsovShortestResetPrefix.result` proves the literal negation of the closed proposition `claim`. Using the actual DFA product and evaluation, the proof checks every two-letter-alphabet word through length four, with the same test for each arbitrary list of that length via its finite index function. The first-factor and product minimality hypotheses bound the words under consideration by the two displayed optima. Their incompatible initial letters give the contradiction.

The claim identity is `sha256:3e3149e6349daf82c455c380d656fc9de98a5c7de1c213fe0a4727a6bde35407`.
The result identity is `sha256:ae44aef38beb643fe6613789cdca111e62959a83e67152c682586b060aa93a74`.
The result uses `Classical.choice`, `Quot.sound`, and `propext`. [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

## Triage

The Tier 1 question is refuted on the optimal-length reading by the displayed three-by-four pair. The finite computation establishes the unique shortest resets of the factors and of the full product.

## ASSUMED-UNVERIFIED

The bounded literature screen in [issue #33847](https://github.com/the-omega-institute/trureturing/issues/33847) found prior direct-product and subset-reset constructions and the feasibility bound. It found no settlement of this optimal-length assertion within the searched scope.

Worldwide priority and completeness of the literature search are unverified.
