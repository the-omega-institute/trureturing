---
bibkey: fokkinkjoshi2025antirecurrence
authors: Robbert Fokkink and Gandhar Joshi
year: 2025
title: "Anti-Recurrence Sequences"
doi: 10.5281/zenodo.18305140
url: https://arxiv.org/abs/2506.13337v1
claim: "Conjecture 4 in arXiv v1 and Conjecture 2 in INTEGERS 26, A24: for every positive integral vector of dimension k > 1, the exact discrepancy A_n-(k*tau+1)n is tau-automatic, where tau is the coefficient sum."
strata_touched:
  - D5/S1/Recurrence/AntiRecurrenceAutomaticity
license: CC-BY-4.0
triage: anchor
---

# Fokkink–Joshi anti-recurrence automaticity

The primary versions are arXiv:2506.13337v1 and INTEGERS 26, A24,
DOI 10.5281/zenodo.18305140. Their corresponding conjectures are
numbered 4 and 2. Both use positive integral coefficient vectors of
dimension k > 1 and trace τ = Σ aⱼ.

The source convention uses strictly increasing complementary positive
sequences with
Aₙ = Σⱼ₌₁ᵏ aⱼ Bₖ₍ₙ₋₁₎₊ⱼ.
The formal coefficient `a j`, for `j : Fin k`, is the source coefficient
aⱼ₊₁. The formal recurrence at natural n is the source recurrence at
n+1. Zero entries of A and B are auxiliary. The output difference is
taken in the integers, with slope kτ+1.

The primary-source qualification identifies both versions as CC BY 4.0.
This entry attributes the problem and definitions to Fokkink and Joshi.
The Lean proof and paired exposition are independently authored; no
source code, experimental data or figures are ported. Earlier work of
Zaslavsky, Bosma and collaborators, and Kimberling and Moses is used
only as bibliographic context reported by the primary source.

The formal theorem constructs a genuine complementary source and
proves its uniqueness before deriving a bounded discrepancy, an exact
inverse-rank local rule and a finite DFAO. It reads the standard base-τ
expansion most significant first and includes every positive index.
The all-ones and other published restricted families are known cases
and receive no separate new credit.
## Verified locator

arXiv:2506.13337v1, https://arxiv.org/abs/2506.13337v1,
Section 1, equation (3), Lemma 3 and Conjecture 4.
The corresponding journal original is INTEGERS 26, A24,
DOI 10.5281/zenodo.18305140, Conjecture 2; its Lemma 2 gives
source existence and uniqueness. The authentic Zenodo record binds
the journal PDF. The coefficient sum, complementary positive-index
convention, recurrence, slope and standard digit interpretation agree
between these versions.

## Literature boundary

The inspected journal original retains the whole conjecture and
proves restricted families, including all-ones and A₁-bounded forms.
Earlier Zaslavsky and Bosma results concern restricted dimensions or
all-ones vectors. Bounded original, citing and status searches found
no earlier arbitrary-positive-vector resolution; repository, pinned
Mathlib and bounded public Lean searches found no exact whole supplier.
These are bounded search conclusions, not worldwide absence or
priority certificates. Later, unindexed, private or unpublished
resolutions and ownership remain outside the verified scope.
The two inspected external Lean automatic-sequence files supply
only definitions and basic facts; no external code or dependency is
used by this result, and their complete NOTICE and compatibility
chains are not claimed to be verified.
