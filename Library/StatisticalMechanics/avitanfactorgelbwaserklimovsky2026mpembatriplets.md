---
bibkey: avitanfactorgelbwaserklimovsky2026mpembatriplets
authors: Ido Avitan; Roee Factor; David Gelbwaser-Klimovsky
year: 2026
title: "Necessary conditions for the Markovian Mpemba effect"
doi: null
url: https://arxiv.org/abs/2603.04567v1
claim: "For a three-level system with detailed-balance rates, the Markovian Mpemba effect requires condition (3) on the rates, one inequality for each value of k. For an N-level system, applying condition (3) to every triplet of levels with the original rates, the authors conjecture that if all triplets violate (3) then the system does not experience the Mpemba effect."
strata_touched:
  - D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation
license: citation-only
triage: anchor
---

# Avitan, Factor and Gelbwaser-Klimovsky, necessary conditions for the Markovian Mpemba effect

I. Avitan, R. Factor and D. Gelbwaser-Klimovsky, *Necessary conditions for the Markovian Mpemba effect*, arXiv:2603.04567 [cond-mat.stat-mech] (v1 of 4 March 2026).

## Verified locator

Source: https://arxiv.org/abs/2603.04567v1

The text was read from the PDF https://arxiv.org/pdf/2603.04567v1:
- p. 2, Eqs. (1)–(2) and the criterion for the Mpemba effect;
- p. 3, Eq. (3) and the triplet construction;
- p. 4, the conjecture.

## Source statements

p. 2: "M is the transition matrix with elements: M_ij = a_ij (i ≠ j), −Σ_{k≠j} a_kj (i = j) (1); a_kj are the transition rates, and we assume that they keep detailed balance: a_jk = a_kj e^{−β_b(E_j−E_k)}" … "Any initial state can be decomposed as a linear combination of the eigenvectors: p(0) = Π(β_b) + Σ_{i=2}^{N} b_i V_i. (2)" … "As shown in [23], the Mpemba effect occurs iff |b_2| has a maximum as a function of the initial inverse temperature, i.e., d|b_2|/dβ_in = 0 for β_in ≠ β_b."

p. 3: "a_{−+}C_{+−} − a_{0+}C_{+0} > a_{−0}(1 − e^{−β_bΔ_{0−}}) k ≥ 1; a_{−+}e^{−β_bΔ_{0−}} > a_{0+} k ≤ 1, (3) where C_ij = 1 + ½e^{−β_bΔ_ij}." … "We call each of these elements a triplet. To each triplet we associate the respective transition rates defined in M, without modifying them."

p. 4: "Based on this numerical result and our zero-temperature theorem, we conject that if for an N−level system, all its triplets violate conditions (3), then the N−level system does not experience the Mpemba effect."

## Reading used by the repository

- For a triplet i < j < k, the levels are − = i, 0 = j, + = k, and k ≡ (a_{−+} + a_{0+})/(a_{−0}(1 + e^{−β_bΔ_{0−}})).
- A triplet violates (3) when neither the k ≥ 1 inequality (with 1 ≤ k) nor the k ≤ 1 inequality (with k ≤ 1) holds.
- The slow-mode coefficient is ℓ·Π(β) for a left eigenvector ℓ of the slowest nonzero eigenvalue, when that eigenvalue is simple. This is b_2 up to a nonzero constant.
- The system shows the Mpemba effect when two initial temperatures on the same side of the bath temperature have the farther one with the smaller |ℓ·Π(β)|. This implies the source's criterion, an interior maximum of |b_2|.
