# The logarithmic cusp on all tails

## Abstract

The symmetric root-spectrum modulus on each tail

**Theorem 1.1 (The sharp two-term estimate for the tail supremum).**

$$\mathit{RH} \Rightarrow \left(\forall r \in \mathbb{R},\; 1 < r \Rightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall U \in \mathbb{R},\; \forall h \in \mathbb{R},\; \left(0 < h \land h \le \frac{r}{2}\right) \Rightarrow \left(\operatorname{Nonempty}\left(\operatorname{V}\left(r, U, h\right)\right) \land \left(\operatorname{BddAbove}\left(\operatorname{V}\left(r, U, h\right)\right) \land \left|\operatorname{sup}\left(\operatorname{V}\left(r, U, h\right)\right) - \frac{h}{\operatorname{s}\left(r\right)} \cdot \left(\operatorname{log}\left(\frac{1}{h}\right) + \operatorname{log}\left(r\right) - 2 \cdot c\right)\right| \le C \cdot h \cdot h\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootTailModulus.root_signal_symmetric_tail_modulus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the centered root spectrum S, let V(r,U,h) be the set of absolute values of S(r,u+h)+S(r,u−h)−2S(r,u) over u at least U. Set s(r)=1/2−1/(2r) and c=(Euler's constant−1+log(2π))/2. The spectrum keeps every actual zero occurrence with its multiplicity.

The symmetric difference factors each unit phase through 2(cos(γh/r)−1). The root coefficient norm is at most r times the reciprocal-square weight. Since 1−cos is nonnegative, the termwise norm sum is exactly the corresponding difference of values of the actual cosine kernel, scaled by 2r/s(r).

Recurrence puts values above every strict lower level of the origin difference in every tail. The supremum lies between that origin difference and the cosine majorant. Both have the same logarithmic and linear coefficients with quadratic errors. The estimate applies to symmetric differences.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootTailModulus.root_signal_symmetric_tail_modulus`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootLateIncrement](RHRootLateIncrement.md)
