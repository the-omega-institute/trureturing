---
slug: monkman-sirker-2023-configurational-entropy-schur-concavity
bibkey: monkman2023symmetry
doi: 10.48550/arXiv.2307.05820
url: https://arxiv.org/abs/2307.05820
triage: theorem
motivation_gids:
  - D5/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy.result
---

# Monkman–Sirker configurational entropy is Schur concave

## Problem

D. Monkman and J. Sirker, *Symmetry-resolved entanglement: general considerations, calculation from correlation functions, and bounds for symmetry-protected topological phases*, J. Phys. A **56** (2023), 495001; arXiv:2307.05820, Section 3.3, “A conjecture on the concavity of Sc”:

> We note that the configurational entropy Sc = S + (−SN) is a sum of a concave and a convex function. Therefore, one cannot directly apply majorization to Sc based on the already obtained results for S and SN. However, this does not rule our that Sc is also a concave function of the parameters {Ck}. Similar to the original Shepp-Olkin paper [22] we will here just investigate the cases M = 2 and M = 3. Based on these results, we conjecture that Sc({Ck}) is indeed Schur concave and majorization thus applies.

For independent Bernoulli variables X₁,…,X_M with probabilities c₁,…,c_M, put N=Σk Xk, S(c)=Σk h(ck) and SN(c)=H(N). Natural logarithms and 0 log 0=0 are used. The claim is that F(c)=Sc(c)=S(c)−SN(c) is Schur concave on [0,1]^M for every natural M: if d has the same coordinate sum as c and every descending partial sum of d is no larger than the corresponding one of c, then F(c)≤F(d).

## Motivation

The entropy of N is Schur concave, as is the sum of binary entropies, but subtracting these two functions does not determine the majorization order of their difference. The theorem establishes the order of the difference itself, including deterministic parameters and the empty vector.

## Gap

The source establishes the small-dimensional motivation M=2 and M=3 and states the unrestricted Schur-concavity conjecture. The theorem here covers every finite dimension. A current independent literature check is not available under the offline constraint; priority beyond the stated source and preregistration is not asserted.

## Route

1. Expand the Bernoulli-sum law as a finite subset sum. Removing two coordinates expresses it as a three-point convolution of the remaining law.
2. For interior parameters p≥q, transfer s from p to q. The direction of the three convolution weights is proportional to (1,−2,1). Bound the entropy derivative of this convolution and compare it with the binary-entropy derivative using the logarithmic divided-difference bound.
3. The resulting nonnegative derivative gives monotonicity up to the pair midpoint. Permutation invariance gives the rest of each T-transform.
4. A finite chain of interior T-transforms establishes the majorization comparison inside the cube.
5. Apply the common affine perturbation c↦ε+(1−2ε)c to both vectors. It preserves majorization, sends the closed cube into its interior for 0<ε<1/2, and tends to the original vector. Continuity gives the closed-cube statement.

## Falsifier

A counterexample would consist of a finite dimension M and two closed-cube vectors c,d with equal sums and every descending partial sum of d bounded by that of c, but F(d)<F(c). The theorem excludes every such pair. A failure of joint concavity would not contradict the Schur-concavity statement.

## Evidence

The D5 modules `PoissonBinomialStructure`, `EntropyDirectionBounds`, `ConfigurationalEntropyStep` and `MonkmanSirkerConfigurationalEntropy` contain the finite-law identities, the entropy-direction estimate, the interior step inequality and the theorem `result : claim`, respectively. The claim quantifies over every natural dimension and every pair of closed-cube parameter vectors related by majorization. No finite enumeration or numerical approximation is used.

## Triage

1. **Proved — conditional-entropy interpretation.** Let X=(X₁,…,X_M). Independence gives H(X)=Σk h(ck), and N is a deterministic function of X, so the Shannon chain rule gives Sc=H(X)−H(N)=H(X|N). This identifies the mathematical meaning of F; the Lean theorem is expressed by finite mass sums rather than a separate probability-space conditional-entropy theorem.

2. **Proved — the pairwise mechanism.** At an interior pair p>q, set A=p(1−q), B=q(1−p), v₀=(1−p)(1−q) and v₂=pq. Then A−B=p−q and AB=v₀v₂. Along the transfer (p,q)↦(p−s,q+s), the derivative of Sc at s=0 factors as

   $$
   (p-q)\left[\frac{\log A-\log B}{A-B}-d\right],
   $$

   where d is the entropy derivative of the remaining-law convolution in direction (1,−2,1). The logarithmic divided-difference estimate A1 controls the binary part:

   $$
   \frac{\log A-\log B}{A-B}\geq\frac{-\log(AB)}{1-AB}\geq-\log(AB).
   $$

   The three-point bound controls the convolution part: d≤−log(v₀v₂)=−log(AB). Thus the derivative is nonnegative. At p=q the derivative is zero, handled without a divided difference. Reapplying the interior statement along the transfer and using the pair permutation yields the full T-transform comparison.

3. **Proved — Schur concavity; open — joint concavity.** The result establishes F(c)≤F(d) whenever d is more mixed than c, including closed-cube boundaries. Joint concavity would require F(tc+(1−t)d)≥tF(c)+(1−t)F(d) for arbitrary c,d and 0≤t≤1. That stronger assertion, mentioned in the source's discussion, is not proved here. Strict Schur concavity and equality classification also remain open here.

4. **Open — Rényi analogues.** No Schur-concavity theorem for a Rényi replacement of either entropy is established here. Such a replacement requires a specified definition of conditional Rényi entropy; the Shannon subtraction identity alone does not supply it.

5. **Open — the Section 4 entanglement bounds.** The Schur-concavity conclusion makes majorization available for Sc under the independent Bernoulli parameterization. Whether the same pairwise derivative mechanism proves further symmetry-resolved entanglement bounds in the source's Section 4 remains open here; this result does not establish new physical bounds from those parameters without the required correspondence and hypotheses.

## ASSUMED-UNVERIFIED

The quoted text and bibliographic journal information are supplied source data. The journal DOI, arXiv version history, forward citations and existence of a later independent resolution have not been checked offline. The arXiv DOI is used. No claim of worldwide priority, joint concavity, Rényi extension, equality classification or new Section 4 bound is made.
