---
bibkey: desogus2026threegates
authors: Marco Desogus
year: 2026
title: "The Three Gates: A Rooted-Operator Approach to Weil Positivity"
doi: null
url: https://arxiv.org/abs/2609.20367v2
claim: The preprint claims all-scale odd-channel Weil positivity via a common-cut Schur induction; this note records its actual-operator proof interfaces without adopting its claimed RH proof as a verified input.
strata_touched: []
license: citation-only
triage: anchor
---

# Common-cut Schur induction: an unadopted all-scale claim

The inspected primary version is [arXiv:2609.20367v2](https://arxiv.org/abs/2609.20367v2), submitted **20 September 2026**, 69 pages. The arXiv history still lists v2 as current at the 1 October inspection. Theorem 0.1 and Theorem 8.7 explicitly claim RH through positivity of the actual localized Weil operator on the real odd logarithmic channel. This is an all-zero claim, distinct from a proportion or fixed-window result. The full proof, external inputs and [supplementary certificates](https://doi.org/10.5281/zenodo.22864087) have not been independently verified here. No counterexample to the main proof was established by the bounded interface review either.

## The actual induction step

At the arithmetic endpoint $a_k=(\log k)/2$, the source retains the pole term in $A_k=C_k-2|s_k\rangle\langle s_k|$. Lemma 6.27, under the old endpoint's positivity and inverse hypotheses, forms the actual harmonic extension

$$
H_k f=\binom{-A_k^{-1}B_{A,k}f}{f},\qquad
B_{A,k}=B_k-2s_kt_k^*,\qquad T_k=H_k^*A_{k+1}H_k.
$$

Theorem 8.5, printed pp.58–59, claims for every integer $k\ge7$, assuming $A_{k,-}>0$, a lower bound on this same extension by a strictly positive ground-coordinate coefficient plus a nonnegative transverse remainder, strictly positive when the transverse component is nonzero. This is the claimed estimate yielding $T_k>0$. The old-block positivity is an induction hypothesis, not an assumption of all-scale positivity. Theorem 1.2's restricted odd Weil criterion and the endpoint-to-all-support closure are separate consumers of the induction.

The load-bearing comparisons to inspect before any reuse are:

- Theorem 6.53 and Theorem 6.55: simultaneous ground/transverse budgets on the same common complement and the required transverse reserve.
- Lemma 8.1: placement of the full actual Schur response, with its positive saving and negative reference charge attached to the same contribution.
- Lemma 8.2: the homogeneous mixed and aligned-forcing estimate for all complex coefficients, not only a normalized scalar case.
- Lemma 8.4: the common-cut, transported form and endpoint-fold identities for the same harmonic vector, including the pole term, actual forcing and physical-pivot positivity.
- Certificate 6.62 and Certificate 8.3: the base at $Y=7$ and the all-$k$ ground margin, whose stated finite interval verification is paired with an analytic tail.

These are propositions that the source claims to prove. They are not merely extra conjectural hypotheses declared by its author; they also have not become independently verified project premises by being listed here. Checking scalar certificates alone would leave the actual-operator and function-space correspondence obligations untouched.

## Relation to the FIB research gap

The retained-old-block, mixed-coupling and Schur-induction architecture is standard and is explicitly attempted at all scales in this source. Naming the support schedule after Fibonacci therefore supplies no architectural novelty. The project's [exact block reduction](../../D5/S3/Weil/ZetaLinear/ExactStickyReduction.lean) and [golden positivity induction](../../D5/S3/Weil/TestFunctions/GoldenPositivityInduction.lean) remain reusable under their own assumptions; this review did not rebuild them.

For an actual finite positive old block $H$, the additional estimate is $B^*H^{-1}B\preceq D$ for the matching new block and coupling; a semidefinite old block also needs the appropriate range condition. This source's claimed budget bridges are relevant candidates for detailed comparison with that obligation. They are not adopted as a supplier that has already closed it. No certificates, zero samples, integer samples or Lean declarations were produced for this source review.
