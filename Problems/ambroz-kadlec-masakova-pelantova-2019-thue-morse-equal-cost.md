---
slug: ambroz-kadlec-masakova-pelantova-2019-thue-morse-equal-cost
bibkey: ambrozetal2019palindromiclength
doi: 10.1016/j.tcs.2019.02.024
url: https://arxiv.org/abs/1812.00711v2
triage: theorem
motivation_gids:
  - D5/S1/Words/Palindromes/ThueMorseAttainment.unbounded_equal_cost
---

# Equal mixed and ordinary palindromic costs on Thue–Morse prefixes

## Problem

Ambrož, Kadlec, Masáková and Pelantová, *Palindromic length of words and
morphisms in class P*, Section 6, final paragraph and Table 2, propose that
the binary Thue–Morse word has prefixes of arbitrarily large ordinary
palindromic length whose combined palindrome–antipalindrome length is equal
to the ordinary palindromic length. The exact source is arXiv:1812.00711v2,
`pallen_classP.tex` lines 678–679, with the journal version in *Theoretical
Computer Science* 780 (2019), 74–83.

The resolved event is the literal statement

> For every natural K with K ≥ 1, there exists a natural n with n ≥ 1 such
> that C(t[0:n)) = PL(t[0:n)) and K ≤ PL(t[0:n)).

Here `t(0)=false`, `t(2r)=t(r)`, and `t(2r+1)=not(t(r))`. `PL` is the
minimum number of nonempty contiguous palindrome factors. `C` is the minimum
number of nonempty contiguous factors each satisfying `Palindrome w` or
`w = map(not, reverse w)`. The word is the literal zero-based fixed point,
with `false=a` and `true=b`; the empty prefix is excluded.

## Motivation

The source asks whether allowing exchange-reversal antipalindromes can leave
ordinary palindromic cost unchanged at arbitrarily high costs. Equality must
hold for the two actual minima on the same literal prefix.

## Gap

The signed-cut lower bound alone does not supply a prefix with equal costs.
An ordinary palindromic upper bound must attain that lower bound on one
positive family with unbounded costs. The attaining-family construction
supplies this missing step.

## Route


The module
`D5/S1/Words/Palindromes/ThueMorseAttainment.lean` proves the exact event in
`unbounded_equal_cost`. It chooses `n = attainingLength K`, where
`attainingLength 0 = 1` and
`attainingLength (m+1) = 4*attainingLength m - 1`. The same module proves
that this family has signed weight, mixed cost and ordinary palindromic cost
all equal to `m+1`. The mixed cost is the actual minimum over consecutive
nonempty factors, and the ordinary cost is the existing `FridPrefix.PL` on
the same literal word.

The family theorem is a supporting lemma for the one quantified event; it is
not a second external problem. The signed cut and factorization arguments are
in `D5/S1/Words/Palindromes/ThueMorseSignedCut.lean`.

## Falsifier

A mismatch between the literal prefix and the constructed word, an empty
factor in a positive factorization, or replacing either minimum by a proxy
would fail the stated event. A failure of the universal cut inequality or of
the ordinary upper bound on the same family would break the sandwich
argument. Finite examples alone cannot establish its universal quantifiers.

## Evidence


The source event and its two forecasts were preregistered in issue
[#26513](https://github.com/the-omega-institute/trureturing/issues/26513),
comment [6633472578](https://github.com/the-omega-institute/trureturing/issues/26513#issuecomment-6633472578).
The source qualification and bounded literature search cover the cited AKMP
paper, Frid's published Fibonacci result, Li's Thue–Morse palindromic-length
work, and Frid–Laborde–Peltomäki's related study. They do not establish a
worldwide priority or novelty result.

The source supplies the motivating assertion and the mixed-cost definition.
The signed cut, substitution transport and attaining-family argument are
repository-derived. The relevant declarations are
`D5/S1/Words/Palindromes/ThueMorseSignedCut.allowed_factor_signed_cut`,
`D5/S1/Words/Palindromes/ThueMorseSignedCut.combined_prefix_signed_lower`,
`D5/S1/Words/Palindromes/ThueMorseAttainment.family_attains` and
`D5/S1/Words/Palindromes/ThueMorseAttainment.unbounded_equal_cost`.

## Triage

### What the settlement shows

Proved by
`D5/S1/Words/Palindromes/ThueMorseSignedCut.allowed_factor_signed_cut` and
`D5/S1/Words/Palindromes/ThueMorseSignedCut.combined_prefix_signed_lower`:
each actual allowed factor increases signed potential by at most one, and
telescoping over consecutive factors gives
`signedWeight(n) ≤ C(t[0:n)) ≤ PL(t[0:n))`.

Proved by
`D5/S1/Words/Palindromes/ThueMorseAttainment.family_attains`:
for the same family `attainingLength 0 = 1`,
`attainingLength (m+1) = 4*attainingLength m - 1`, all three quantities are
`m+1`. The substitution `tau(b) = [b,not b,not b,b]` transports nonempty
palindrome factorizations to nonempty palindrome factorizations and identifies
the substituted literal prefix with the prefix of four times the length.
The one-letter deletion bound gives the ordinary upper bound after removing
the last letter. Nonadjacent signed digits give the matching signed weight.
Thus the universal lower bound is sharp on this family, and allowing
antipalindromes does not shorten these prefixes.

Proved by
`D5/S1/Words/Palindromes/ThueMorseAttainment.unbounded_equal_cost`:
choosing `n = attainingLength K` for each `K ≥ 1` proves the complete stated
event. The family theorem supports this single external assertion; it is not
a second external problem.

Open: this argument does not determine either minimum for every prefix,
characterize all equality prefixes, or establish corresponding claims for
shifted windows, arbitrary factors or other words. No hypotheses are relaxed
beyond the stated literal binary word and the two factorization definitions.
The source's finite examples are consistent with the event but are not its
universal proof. Consequences for other results or questions in the source,
including other words and all-factor asymptotics, remain open here unless
separately supplied with a proof; none is inferred from this prefix-family
settlement.

### Source-binding audit and scope

The source-binding audit has four explicitly unresolved targets under issue
[#26539](https://github.com/the-omega-institute/trureturing/issues/26539):

- `D5.S1.Words.Palindromes.ThueMorse.allowed_factor_signed_cut`;
- `D5.S1.Words.Palindromes.ThueMorse.combined_prefix_signed_lower`;
- `D5.S1.Words.Palindromes.ThueMorse.family_attains`;
- `D5.S1.Words.Palindromes.ThueMorse.unbounded_equal_cost`.

The existing registration for
`D5.S1.Words.Palindromes.ThueMorse.transition_period_doubling` remains
validated. No unresolved target is classified as validated. The linked-issue
exception permits the mathematical delivery while those source-binding
certificates remain open.

This resolution concerns the exact standard binary Thue–Morse prefixes and
the two stated minima. It makes no claim about other words, shifted windows,
derivative or proxy costs, finite tables as universal evidence, or worldwide
openness.

## ASSUMED-UNVERIFIED

The bounded literature and repository searches recorded above are not an
exhaustive global search. The source-to-Lean correspondence is stated by the
definitions and dossier, while the kernel-checked theorem supplies the
formal event under those definitions.
