---
bibkey: johnston2025knutson
authors: Dylan Johnston; Diego Martín Duro; Dmitriy Rumynin
year: 2025
title: Global Representation Ring and Knutson Index
doi: 10.1080/00927872.2025.2498055
url: https://arxiv.org/abs/2403.18498v6
claim: "Section 2 defines regular elements, the Knutson index and S-subindex; Question 2.5 asks whether one finite subset computes every index."
strata_touched:
  - D5/S3/HomologicalAlgebra/KnutsonFiniteSubindexRefutation
license: citation-only
triage: anchor
---

# Knutson indices and finite subsets

## Verified locator

DOI: 10.1080/00927872.2025.2498055

Source: https://arxiv.org/abs/2403.18498v6

The source is version 6, Section 2, published in Communications in Algebra
53(11), 4793–4804. The definitions are on published page 4794 and
Question 2.5 is on page 4795.

## Source statements

Section 2, p. 4794:

> Let R be a finitely generated commutative ring. Suppose that R is equipped with a ring homomorphism α: R → ℤ.

> We call an element r ∈ R regular if α(r) ≠ 0 and x·r = α(x) r for all x ∈ R.

Definition 2.1, p. 4794:

> The Knutson Index 𝒦_r(x) of an element x ∈ R with respect to a regular element r ∈ R is the non-negative integer m such that Rx ∩ ℤr = mℤr.

Definition 2.2, p. 4794:

> Let S ⊂ R be a subset, and for any x ∈ R define S(x) = {s ∈ S: s·x ∈ ℤr}.

> Associated to S(x) we also set Ind(x) = {m ∈ ℤ: s·x = m·r for s ∈ S(x)}.

> Define the Knutson S-subindex of x ∈ R with respect to the regular element r ∈ R as 𝒦_r^S(x) := gcd(Ind(x)).

> By convention, if S(x) = ∅ then we set 𝒦_r^S(x) = ∞.

The S-subindex is gcd(Ind(x)). For regular r, the coefficient of r is
unique. The Lean definition chooses that coefficient for an eligible
multiplier and uses zero otherwise, then takes the gcd of absolute values.
The ordinary index is the least positive coefficient, or zero if no positive
coefficient exists. These are the expressions specified in issue #19214.

Question 2.5, p. 4795:

> Does there exist a finite subset S ⊂ R such that for all x ∈ R we have 𝒦_r(x) = 𝒦_r^S(x)?

The affirmative proposition quantifies over all rings in the setting of
Section 2. The formal refutation uses a commutative ring with five integer
coordinates. Its augmentation is d + 2a + 2b + 4t. The elements
X(k) = (0,1,2k,0,−k) and Y(k) = (0,1,−2k,0,k) multiply to
r = (0,0,0,0,1). For each finite S the parameter
k = 1 + ∑(s ∈ S) |s.b| makes every eligible coefficient even, while
X(k) has ordinary index one.

Proposition 2.6 retains the affirmative answer for reduced rings. The
source explicitly states that this covers its other rings, which embed
in a finite product of copies of ℂ. The refutation does not invalidate
that proposition or those applications.

## Literature boundary

The supplied literature screen checked the source and later or citing
manuscripts arXiv:2409.06375, 2306.12408, 2211.08123, 2507.21316,
2503.10590, 2309.07238, 2404.16618 and 2304.07525. No settlement was
located in that screen. Completeness is ASSUMED-UNVERIFIED: citation APIs
were rate-limited, and Carl Faith, “Annihilator ideals, associated primes
and Kasch-McCoy commutative rings”, DOI 10.1080/00927879108824235,
was not read beyond bibliographic metadata.
