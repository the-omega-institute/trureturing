---
bibkey: ellis2022cutfamilya
authors: Paul Ellis; Thotsaporn Aek Thanatipanonda
year: 2022
title: The Arithmetic-Periodicity of cut for C = {1, 2c}
doi: 10.1016/j.dam.2022.08.027
url: https://arxiv.org/abs/2203.02457v1
claim: Conjecture 1 states that every Family A cut-set has nim-sequence (0, 1)^c (+2).
strata_touched:
  - D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1016/j.dam.2022.08.027

Source: https://arxiv.org/abs/2203.02457v1

Published in Discrete Applied Mathematics 322, 391–403. The author copy at
https://thotsaporn.com/PartitionGame.pdf states Conjecture 1 unchanged.
Page numbers below refer to arXiv v1.

## Nim-sequence and options

Page 2:

> Fixing a cut-set C, we write G(n) to denote the nim-value of the position of cut with a single pile of size n. Then G(n) is called the nim-sequence of the game with cut-set C.

Definition 1, page 2:

> Given a pile of size n, an option O_n is a sequence of piles obtainable via a single legal move on that pile. In other words, O_n is a particular partition of n with d + 1 parts for some d ∈ C. Formally, O_n = (h_0, h_1, ..., h_d) where 1 ≤ h_i and h_0 + h_1 + · · · + h_d = n.

Page 3:

> The notation (0, 1)^3 (+2), for example, denotes the sequence 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 4, 5, 4, 5, 4, 5, . . ..

The formal recursion uses Fin (d + 1) for the parts, List.ofFn and a right
fold of Nat.xor for their nim-sum, and the existing set-valued mex owner.
The recursion guard is inactive on legal Family A options because each part
is smaller than the original pile.

## Family A and Conjecture 1

Section 7, page 18:

> Let X to be a non-empty set of even numbers, each of which is at least 4. Let Y to be a non-empty set of odd numbers, each of which is at least 5. Let x = 2c and y be the smallest elements of X and Y, respectively.

> Family A: C = {1, 3} ∪ X, or C = {1, 3} ∪ X ∪ Y.

> We already know from [DDLP, Propositions 8] that the nim-sequence for C = {1, 3, 2c} is (0, 1)^c (+2).

Conjecture 1, page 18:

> The nim-sequence for all games of cut in this family are all precisely (0, 1)^c (+2).

The sequence begins at n = 1. Its term is
2⌊(n − 1)/(2c)⌋ + ((n − 1) mod 2). The first Family A alternative is
represented by Y = ∅, and the second by nonempty Y. The least element
of the nonempty natural set X is sInf X = 2c. X and Y may be infinite;
only cut sizes smaller than a given pile can contribute an option.

## Scope and literature

Dailly–Duchêne–Larsson–Paris, “Partition games”, arXiv:1803.02621v3,
Proposition 8 (DOI 10.1016/j.dam.2020.05.032), proves the base case
C = {1, 3, 2c}. No new method is claimed for that base case.
The full-family proof excludes every extra odd cut by its low bit and every
extra even cut by the quotient budget. Reachability uses only 1, 3 and 2c.

The literature screen in
https://github.com/the-omega-institute/trureturing/issues/19674 covers the
arXiv and journal author copies, Semantic Scholar, OpenAlex and the later
author works listed there. Completeness is ASSUMED-UNVERIFIED: citation
coverage is incomplete and not every later proof was independently read.
