# Affine Feedback Threshold

## Abstract

An affine feedback map contracts below unit gain, expands above it, and is critical at one.

**Theorem 1.1 (Affine feedback has a unit-gain threshold).**

$$\begin{gathered}\forall a, b\in\mathbb{R},\\f(x)=a+bx, x^{*}=\frac{a}{1-b},\\(0\leq b<1\Rightarrow \operatorname{Contracting}(f,b)\land (\forall x, (f(x)=x\Leftrightarrow x=x^{*})\land f^{n}(x)\to x^{*})),\\(1<b\Rightarrow f(x^{*})=x^{*}\land (\forall x\neq x^{*}, \operatorname{dist}(f(x), x^{*})=b\operatorname{dist}(x, x^{*})>\operatorname{dist}(x, x^{*}))),\\(b=1\Rightarrow \forall x, y, \operatorname{dist}(f(x), f(y))=\operatorname{dist}(x, y)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/AffineFeedbackThreshold.affine_feedback_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f(x) = a + bx on the active affine region and let x* = a/(1-b) away from unit gain. If b is nonnegative and strictly below one, f is a contraction, x* is its unique fixed point, and every affine iterate converges to x*.

If b is greater than one, x* remains fixed and every nonzero deviation from it is multiplied in distance by b, hence strictly amplified. At b = 1, the map preserves every pairwise distance.

Pinned Mathlib and Loogle supplied the exact contraction declarations ContractingWith.fixedPoint_unique and ContractingWith.tendsto_iterate_fixedPoint, both applied by the module. Local and repository searches found no declaration packaging all three gain regimes; LeanSearch returned HTTP 404.

## References

- Truth anchor: `D5/S1/FixedPoints/AffineFeedbackThreshold.affine_feedback_threshold`
