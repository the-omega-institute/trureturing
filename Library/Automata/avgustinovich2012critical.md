---
bibkey: avgustinovich2012critical
authors: S. Avgustinovich, J. Karhumäki and S. Puzynina
year: 2012
title: On abelian versions of critical factorization theorem
doi: 10.1051/ita/2011121
url: https://www.numdam.org/item/ITA_2012__46_1_3_0/
claim: "Open problem 6.2 asks whether two centered abelian period lengths can occur at every position of a non-periodic biinfinite word."
strata_touched:
  - D5/S1/Words/TwoCenteredAbelianPeriods
license: citation-only
triage: anchor
---

# Two centered abelian period lengths

## Verified locator

DOI: 10.1051/ita/2011121

Source: https://www.numdam.org/item/ITA_2012__46_1_3_0/

RAIRO – Theoretical Informatics and Applications 46(1), 3–15,
Section 2.2, p. 6, and Open problem 6.2, p. 14.

## Source statements

Section 2.1, p. 4:

> We say that a biinfinite word w is periodic, if there exists a finite word v such that w = v^ℤ.

Section 2.2, p. 6:

> Two words u and v in Σ∗ are abelian equivalent if and only if |u|ₐ = |v|ₐ for all a ∈ Σ.

> An abelian k-power is a non-empty word of the form u = v₁v₂…v_k where the words vᵢ are pairwise abelian equivalent. In this case we refer to |v₁| as the length of an abelian period of u (or briefly period).

> Let w be a biinfinite word over an alphabet Σ. For integer i, by a position i in a word w we mean a position between wᵢ and wᵢ₊₁.

> for every i there exists l′ ≤ l such that w_{i−l′k+1} … w_{i+l′k} is an abelian 2k-power.

The fixed-length predicate displays this centered factor at a specified
period length l. Its 2k consecutive blocks each have length l.

Open problem 6.2, p. 14:

> Let k be an integer. Does there exist a non-periodic word w and integers l₁, l₂, such that w contains a central abelian 2k-power of length l₁ or l₂ at every position?

> Notice that the construction from Theorem 3.2 gives an example of such a word using three periods. One period trivially implies periodicity. So two periods is an open question.

## Mathematical scope

The finite alphabet is encoded as Fin r, and a biinfinite word as
a function from the integers to Fin r. Positions are cuts after wᵢ.
Nonempty blocks have positive natural length. Letter counts use
AbelianBorderQuestionDefs.letterCount. CentralAbelianPower compares all
2k blocks with the first, and Periodic means the existence of a positive
natural period. The result proves that every such word is periodic for
each k ≥ 1. Its proof gives lcm(l₁,l₂) when both lengths are positive;
a zero length cannot satisfy CentralAbelianPower and leaves the
single positive length.

The decisive identity expresses the negative square of a mixed forward
difference as the increment of a bounded integer flux. The flux is
antitone, is constant on both tails, and becomes a bounded coboundary
there. Bounded constant drift forces both tail values to be zero, hence
every mixed difference is zero. Applying this to each letter count
recovers ordinary periodicity.

## Literature boundary

The bounded literature screen covers the source, the Fici–Puzynina
survey arXiv:2207.09937v2, and the full Huova–Karhumäki–Saarela–Saari
chapter.
No prior answer was identified in that bounded screen. Completeness of
the citing-paper and author-publication screen is ASSUMED-UNVERIFIED;
no worldwide priority assertion follows. The one-sided two-period
Sturmian examples and the unrestricted bounded centered-square question
have different hypotheses.
