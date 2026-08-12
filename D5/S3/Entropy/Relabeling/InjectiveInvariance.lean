/- GID: D5/S3/Entropy/Relabeling/InjectiveInvariance
   generality: G
   mirror-B: D5/B/S3/Entropy/Relabeling/InjectiveInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Discrete Shannon entropy is invariant under injective relabeling of the support: for an injective f : ι → κ and arbitrary real weights p : ι → ℝ, the pushforward extend f p 0 (p on the image of f, 0 off it) has the same shannonEntropy as p. This is the discrete-entropy-column identity H(f(X)) = H(X) for injective f. Proof: rewrite the ι-sum through extend on the image via injectivity (sum_image), then extend to the full index type since off-image terms are negMulLog 0 = 0 (sum_subset). Holds for arbitrary weights, not only probability distributions. The strict-decrease remark for non-injective merging of positive-mass atoms is not covered. -/

import D5.S3.Entropy.MaxEntropy
import Mathlib

open Real BigOperators

namespace D5.S3.Entropy.Relabeling.InjectiveInvariance

open D5.S3.Entropy.MaxEntropy

/-- **Discrete Shannon entropy is invariant under injective relabeling.** For an injective
`f : ι → κ` and arbitrary real weights `p : ι → ℝ`, the pushforward `Function.extend f p (fun _ => 0)`
— which equals `p` on the image of `f` and `0` off it — has the same `shannonEntropy` as `p`:
`shannonEntropy (Function.extend f p 0) = shannonEntropy p`.

This is the discrete-entropy-column identity `H(f(X)) = H(X)` for `f` injective on the support:
relabeling by an embedding (not merely a bijection/permutation) into a possibly-larger index type,
padded with `0` off the image, preserves the entropy — because injectivity preserves the multiset of
probabilities and the padding contributes `negMulLog 0 = 0`. The statement holds for **arbitrary** real
weights `p`, so probability distributions are the special case; this generalises the coordinate-swap
invariance of joint entropy already in the entropy domain.

The proof rewrites the `ι`-indexed sum through `f` on `Finset.univ.image f` (injectivity, via
`Finset.sum_image`), then extends to the full index type `κ` by `Finset.sum_subset`, the off-image
terms vanishing since `Function.extend_apply'` gives the pad value `0` and `Real.negMulLog_zero = 0`.

Only the injective-invariance equality is recorded; the strict-decrease remark — that a non-injective
`f` merging positive-mass atoms strictly *decreases* the entropy — is not covered. -/
theorem shannonEntropy_extend_injective
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : ι → κ} (hf : Function.Injective f) (p : ι → ℝ) :
    shannonEntropy (Function.extend f p (fun _ => 0)) = shannonEntropy p := by
  classical
  unfold shannonEntropy
  set G : κ → ℝ := fun j => Real.negMulLog (Function.extend f p (fun _ => 0) j) with hG
  have step1 : ∑ i, Real.negMulLog (p i) = ∑ i, G (f i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hG, hf.extend_apply]
  have step2 : (∑ i, G (f i)) = ∑ j ∈ Finset.univ.image f, G j :=
    (Finset.sum_image (fun x _ y _ h => hf h)).symm
  have step3 : (∑ j, G j) = ∑ j ∈ Finset.univ.image f, G j := by
    refine (Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => ?_)).symm
    have hjr : ¬ ∃ i, f i = j :=
      fun ⟨i, hi⟩ => hj (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hi⟩)
    simp only [hG, Function.extend_apply' _ _ _ hjr, Real.negMulLog_zero]
  rw [step1, step2]; exact step3

end D5.S3.Entropy.Relabeling.InjectiveInvariance
