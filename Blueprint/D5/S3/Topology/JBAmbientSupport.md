# Ambient idempotent support

## Abstract

Ambient order domination by an idempotent forces support in its Peirce two-space on the original complete real six-law JB carrier.

Let X be any complete real normed vector space, S its specified real bilinear product, and u its specified unit. Data(X,S,u) consists of symmetry, the unit law, the Jordan identity, product norm domination, the square norm identity and square monotonicity. Write K(y) for the existence of z in this same X with S(z,z)=y, and write U(r,y)=2 S(r,S(r,y))-S(S(r,r),y). The zero space and zero idempotent are included.

**Theorem 1.1 (Domination forces support).**

$$\forall X \in CompleteRealNormedSpaces,\; \forall S \in RealBilinearMaps\left(X\right),\; \forall u \in X,\; Data\left(X, S, u\right) \Rightarrow \left(\forall p \in X,\; \forall x \in X,\; \forall c \in Reals,\; \left(S\left(p, p\right) = p \land \left(K\left(scale\left(c, p\right) + x\right) \land K\left(scale\left(c, p\right) - x\right)\right)\right) \Rightarrow S\left(p, x\right) = x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/JBAmbientSupport.support_of_squares` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set q=u-p and g(t)=U(u+tq,cp+x), h(t)=U(u+tq,cp-x). The original quadratic positivity theorem makes g(t) and h(t) actual squares for every real t. Bilinear expansion gives g(t)+h(t)=2cp and g(t)-g(-t)=4t S(q,x). Square monotonicity gives norm(g(t))<=2 norm(cp), hence abs(t) norm(S(q,x))<=norm(cp) uniformly in t. If S(q,x) is nonzero, t=(norm(cp)+1)/norm(S(q,x)) contradicts this bound. Therefore S(q,x)=0 and S(p,x)=x. No sign restriction on c is needed for this implication.

**Theorem 1.2 (The original norm bounds supported vectors).**

$$\forall X \in CompleteRealNormedSpaces,\; \forall S \in RealBilinearMaps\left(X\right),\; \forall u \in X,\; Data\left(X, S, u\right) \Rightarrow \left(\forall p \in X,\; \forall x \in X,\; \left(S\left(p, p\right) = p \land S\left(p, x\right) = x\right) \Rightarrow \left(K\left(scale\left(norm\left(x\right), p\right) + x\right) \land K\left(scale\left(norm\left(x\right), p\right) - x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/JBAmbientSupport.squares_of_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original ambient center theorem makes norm(x)u+x and norm(x)u-x squares. Apply the original positive quadratic map U(p), which sends u to p and fixes x. Thus both norm(x)p+x and norm(x)p-x are actual ambient squares. Together with domination forcing support, this identifies the Peirce two-space with the vectors bounded above and below by a nonnegative scalar multiple of p. It does not assert equality with the corner's internal square cone.

**Theorem 1.3 (The square bound in the same ambient cone).**

$$\forall X \in CompleteRealNormedSpaces,\; \forall S \in RealBilinearMaps\left(X\right),\; \forall u \in X,\; Data\left(X, S, u\right) \Rightarrow \left(\forall p \in X,\; \forall a \in X,\; \left(S\left(p, p\right) = p \land S\left(p, a\right) = a\right) \Rightarrow K\left(scale\left(square\left(norm\left(a\right)\right), p\right) - S\left(a, a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/JBAmbientSupport.corner_square_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specializing the existing polarized Jordan identity to p,p,a,a gives S(p,S(a,a))=S(a,a). The preceding supported-vector bound applied to S(a,a), and the original square norm identity, give norm(a)^2 p-S(a,a) as an actual square. Its root is required only in X. These consequences use the original product and norm and impose no square-root closure on a dense original subalgebra.

## References

- Truth anchor: `D5/S3/Topology/JBAmbientSupport.corner_square_bound`
- Truth anchor: `D5/S3/Topology/JBAmbientSupport.squares_of_supported`
- Truth anchor: `D5/S3/Topology/JBAmbientSupport.support_of_squares`
- Dependency: [D5/S3/Topology/JBComplexification](JBComplexification.md)
