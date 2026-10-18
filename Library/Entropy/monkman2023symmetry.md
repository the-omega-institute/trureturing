---
bibkey: monkman2023symmetry
authors: D. Monkman; J. Sirker
year: 2023
title: "Symmetry-resolved entanglement: general considerations, calculation from correlation functions, and bounds for symmetry-protected topological phases"
doi: 10.48550/arXiv.2307.05820
url: https://arxiv.org/abs/2307.05820
claim: "Section 3.3 conjectures that the configurational entropy Sc = S − SN is Schur concave in the Bernoulli parameters Ck. Here S is the sum of binary entropies and SN is the Shannon entropy of their independent Bernoulli sum. The authors investigate M = 2 and M = 3."
strata_touched:
  - D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure
  - D5/S3/Entropy/PoissonBinomial/EntropyDirectionBounds
  - D5/S3/Entropy/PoissonBinomial/ConfigurationalEntropyStep
  - D5/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy
license: citation-only
triage: anchor
---

# Monkman–Sirker, symmetry-resolved entanglement

D. Monkman and J. Sirker, *Symmetry-resolved entanglement: general considerations, calculation from correlation functions, and bounds for symmetry-protected topological phases*, Journal of Physics A: Mathematical and Theoretical **56** (2023), 495001; arXiv:2307.05820. The identifier above is the arXiv DOI; the journal DOI is not independently confirmed here.

## Locator

DOI: 10.48550/arXiv.2307.05820
Source: https://arxiv.org/abs/2307.05820

Section 3.3, “A conjecture on the concavity of Sc”, arXiv:2307.05820. The quotation is the source text supplied for this problem; no particular arXiv version or page number is asserted.

## Source statement

> We note that the configurational entropy Sc = S + (−SN) is a sum of a concave and a convex function. Therefore, one cannot directly apply majorization to Sc based on the already obtained results for S and SN. However, this does not rule our that Sc is also a concave function of the parameters {Ck}. Similar to the original Shepp-Olkin paper [22] we will here just investigate the cases M = 2 and M = 3. Based on these results, we conjecture that Sc({Ck}) is indeed Schur concave and majorization thus applies.

## Reading used by the repository

For every natural M, the parameters form a vector c : Fin M → [0,1]. Independent Bernoulli variables Xk have success probabilities ck, and N is their sum. The two entropies are S = Σk h(ck) and SN = −Σn P(N=n) log P(N=n), with natural logarithms and 0 log 0 = 0. The conjectured conclusion is Schur concavity: if d is more mixed than c, with the same coordinate sum and no greater descending partial sums, then Sc(c) ≤ Sc(d).

The repository's `result` proves this majorization comparison on the closed cube in every finite dimension. Joint concavity in the full parameter vector, strictness, equality cases, Rényi analogues, and extensions of the pairwise argument to the entanglement bounds of Section 4 are not conclusions of that theorem.

## Literature and formalization boundary

The supplied quotation identifies the named assertion; it does not establish the absence of subsequent proofs. No independent current publication-absence check or worldwide priority claim is made. The finite-dimensional majorization proof is derived in the repository, while the entropy definitions and conjecture are attributed to the source.

This citation-only note incorporates no source software. The formal theorem covers every natural dimension and every closed-cube Bernoulli parameter vector, including deterministic coordinates. The conditional-entropy interpretation follows from independence and the Shannon chain rule; it is not a separate conditional-entropy theorem in these Lean modules.
