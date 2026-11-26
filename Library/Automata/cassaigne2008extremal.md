---
bibkey: cassaigne2008extremal
authors: Julien Cassaigne
year: 2008
title: On extremal properties of the Fibonacci word
doi: 10.1051/ita:2008003
url: https://www.numdam.org/item/10.1051/ita:2008003.pdf
claim: "Open problem 2 asks whether equality of the asymptotic index and recurrence quotient characterizes Sturmian words."
strata_touched:
  - D5/S1/Words/Complexity/CassaigneSturmianCharacterization
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1051/ita:2008003

Source: https://www.numdam.org/item/10.1051/ita:2008003.pdf

RAIRO. Theoretical Informatics and Applications 42(4), 701–715.
The page numbers below refer to the printed journal pagination.

## Source statements

Printed p. 707, Open problem 2:

“Open problem 2. How can this equality be explained? Does it characterize Sturmian words? (Compare, for instance, with the Prouhet-Thue-Morse word which has ind*(t) = 2 and ρ*(t) = 10, see Prop. 6.1.)”

The preceding sentence is: “If u is a Sturmian word, then ρ*(u) = ind*(u).”
The characterization question asks whether the converse holds.

Printed p. 701:

“Lₙ(u) denotes the language of factors of length n of u (i.e., finite words of length n that occur as a block of consecutive letters of u) and L(u) the language of all factors of u.”

Printed p. 702:

“A word u ∈ Bᴺ is called a Sturmian word of slope α when there exists β ∈ R such that one of the following holds: (i) for all n ∈ N, uₙ = a if and only if ⌊αn + β⌋ = ⌊α(n + 1) + β⌋; (ii) for all n ∈ N, uₙ = a if and only if ⌈αn + β⌉ = ⌈α(n + 1) + β⌉.”

The slope lies in [0,1] and is irrational. The binary encoding uses Bool,
with true representing a, false representing b, and natural indices starting
at zero.

Printed p. 702, Section 2.1:

“The exponent e(w) of a word w ∈ A* is the maximum of |w|/|z| over all words z ∈ A+ such that w is a prefix of zω.”

Printed pp. 703–704, Section 2.2:

“ind*(u) = lim supₙ→∞ {e(w) : w ∈ L(u) and |w| ≥ n} ∈ [1, +∞].”

Printed p. 706, Section 3:

“R(n) = inf{N ∈ N : ∀w ∈ Lᴺ(u), Lₙ(w) = Lₙ(u)} ∈ N ∪ {+∞}”

“ρ*(u) = lim supₙ→∞ R(n)/n ∈ [1, +∞].”

The recurrence infimum uses ENat, so an empty set of finite bounds has value
top. Ratios and asymptotic suprema use ENNReal and preserve this infinite
value. A finite word has a positive period at least its length; its least
positive period is a natural number.

## Scope

The negative answer concerns the converse implication for infinite binary
words. Uniform replication of each letter of the golden word supplies the
family. It does not refute the forward implication for Sturmian words or the
finite-scale characterization in Masáková–Pelantová, arXiv:0809.0603v2.
The paper has no arXiv identifier. Literature-search completeness remains
ASSUMED-UNVERIFIED.
