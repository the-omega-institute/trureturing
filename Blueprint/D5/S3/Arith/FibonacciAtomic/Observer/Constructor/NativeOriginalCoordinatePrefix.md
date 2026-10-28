# Original prefixes from finite native image data

## Abstract

Additive finite lookahead and executable decoding of actual native image prefixes.

A completed native tree is either an alpha leaf, a beta leaf, or an ordered pair. Arbitrary infinite and non-rational trees are included. An address is a finite list of Bool child choices. Its reply is alpha, beta, branch, or absent. Descendants of a leaf are absent. The native substitution rho maps alpha to beta, beta to the pair (beta,alpha), and preserves pairs. The finite Source substitution has the same action. Powers include zero.

Put H(s)=max(height(substitution^s(alpha)),height(substitution^s(beta))). These are actual finite terminal trees; the height of a leaf is zero and the height of a pair is one plus the larger child height. Thus H(0)=0. cutoff(d,X) retains all replies strictly above depth d, with holes only at reached positions of depth d. Inclusive depth h therefore uses cutoff h+1.

**Theorem 1.1 (Additive image agreement determines original agreement).**

$$\forall s: Nat, (\forall h: Nat, (\forall U: CompletionTree, (\forall V: CompletionTree, ((\forall p: Address, (\operatorname{length}\left(p\right)\le h+\operatorname{H}\left(s\right) \implies \operatorname{reply}\left(p, \operatorname{rhoPower}\left(s, U\right)\right) = \operatorname{reply}\left(p, \operatorname{rhoPower}\left(s, V\right)\right))) \implies (\forall p: Address, (\operatorname{length}\left(p\right)\le h \implies \operatorname{reply}\left(p, U\right) = \operatorname{reply}\left(p, V\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalCoordinatePrefix.inverse_prefix_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quantifiers range over every natural s,h and arbitrary completed originals U,V. Image agreement is required at every address of length at most h+H(s). The conclusion is agreement of the originals at every address of length at most h, including absent descendants. Equivalently the images can be any two members of the actual language L_s, with U,V their unique actual preimages.

Agreement through the finite height of a terminal forces a completed tree to equal that terminal. Applying this to the two actual leaf images, then using injectivity of rho^s, distinguishes leaves from each other and from a pair. If both originals are pairs, their images are pairs with exactly the images of the original children. Descending to a child consumes one level on both sides. H(s) is added once at the root, rather than at every ancestor.

**Theorem 1.2 (A finite decoder recovers every promised-image prefix).**

$$\forall s: Nat, (\forall d: Nat, (\forall X: CompletionTree, (\operatorname{decodePrefix}\left(s, d, \operatorname{cutoff}\left(\operatorname{H}\left(s\right)+d, \operatorname{rhoPower}\left(s, X\right)\right)\right) = \operatorname{cutoff}\left(d, X\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalCoordinatePrefix.decode_prefix_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

decodePrefix(s,d) has only a finite pattern of depth H(s)+d as input and returns a finite original pattern of depth d. It takes no completed tree, infinite image oracle, choice function or inverse service as an argument. At zero output depth it returns the single hole. At positive depth it compares the current finite image pattern against the actual finite alpha and beta image terminals. terminalMatch visits only the finite terminal's own addresses, stopping at each terminal leaf; a terminal of height at most H(s) needs no reply deeper than H(s) below the current address. A successful comparison returns the corresponding original leaf. Otherwise a pair pattern is decoded recursively on its two child patterns. An off-image leaf pattern has a total fallback, with no correctness claim outside promised actual images.

Terminal isolation and native injectivity prove that on an actual image a successful comparison occurs exactly for the corresponding original leaf. A true original pair therefore takes the recursive case. Induction on requested output depth proves the displayed equality for every completed original X. Recovered leaves encode absent descendants without exploring them. The statement includes s=0, output depth zero, inclusive h=0 by d=1, and completed outputs that have no finite rational presentation.

Application to an actual canonical image uses NativeFunctionalEffectivePrefix.prefixProgram(S,mode,p,R,H(s)+h,i) at supplied shared parameters p and inclusive depth H(s)+h, followed by decodePrefix(s,h+1). The existing effective_prefix theorem identifies this finite image program with the cutoff of the canonical value of R(i). Once the actual normalization/reconstruction bridge identifies that same canonical value as rho^s of the desired original, the decoder equality gives its original cutoff h+1. This composition introduces no infinite-tree oracle. The current module supplies the decoder; it does not establish the missing common-shift reconstruction bridge, the finite symbolic inverse q+s=n, a Presburger partition, or canonical finite rigidity for every normalized original coordinate. The full source theorem and unrestricted acquired-input obligations remain open. No runtime inverse port or physical query-cost theorem is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalCoordinatePrefix.decode_prefix_correct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalCoordinatePrefix.inverse_prefix_agreement`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate](../../ActualImageAddressCertificate.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalEffectivePrefix](NativeFunctionalEffectivePrefix.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeImageSaturationInterface](NativeImageSaturationInterface.md)
