# Arimoto hyperbolic elasticity

## Abstract

The hyperbolic elasticity of the binary Arimoto coordinate increases below order one and from one through three halves.

**Definition 1.1 (Hyperbolic elasticity).**

$$\forall b \in \mathbb{R},\; \forall s \in \mathbb{R},\; \operatorname{elasticity}\left(b, s\right) = \frac{b \cdot \operatorname{sinh}\left(s\right) \cdot \operatorname{cosh}\left(s\right)^{2}}{\operatorname{sinh}\left(b \cdot s\right) \cdot \operatorname{cosh}\left(\left(b + 1\right) \cdot s\right)}$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/ArimotoHyperbolic.elasticity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

With b=alpha-1 and t=tanh(s), this quotient is the elasticity t psi''(t)/psi'(t) of psi(t)=k(alpha,(1-t)/2). The total quotient is used only at s>0 and b≠0.

**Theorem 1.2 (Increasing elasticity).**

$$\forall b \in \mathbb{R},\; \left(\left(0 - 1 < b \land b < 0\right) \lor \left(0 < b \land b \le \frac{1}{2}\right)\right) \Rightarrow \operatorname{StrictMonoOn}\left(\operatorname{elasticity}\left(b\right), \operatorname{Ioi}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/ArimotoHyperbolic.strictMonoOn_elasticity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

For s>0 the functions r cosh(rs)/sinh(rs) and r sinh(rs)/cosh(rs) strictly increase for r>0. Mathlib’s inequality 2z<sinh(2z), together with the double-angle identity, gives sinh(z)cosh(z)>z for the first comparison. The elasticity derivative divided by the positive elasticity is coth(s)+2tanh(s)-b coth(bs)-(b+1)tanh((b+1)s). For -1<b<0, oddness of sinh replaces b by -b in the coth term; both comparisons give positivity. For 0<b≤1/2, parameter comparison reduces the sign to b=1/2. At that endpoint the quotient equals cosh(s)^2/(2cosh(s)-1), whose derivative is 2cosh(s)(cosh(s)-1)sinh(s)/(2cosh(s)-1)^2>0. No logarithm of a negative sinh value and no numerical sign test is used.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/ArimotoHyperbolic.elasticity`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/ArimotoHyperbolic.strictMonoOn_elasticity`
