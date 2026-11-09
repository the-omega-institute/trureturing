# Geometric Scale Rigidity

## Abstract

A continuous profile constant on a shrinking geometric orbit takes its value at zero.

**Theorem 1.1 (Geometric-orbit rigidity at the limiting point).**

$$\forall (h : (\mathbb{R} \to \mathbb{R})), \forall (rho : \mathbb{R}), \forall (M : \mathbb{R}), ((\operatorname{ContinuousAt}\left(h, 0\right)) \land (0 \le rho) \land (rho < 1) \land (\forall (n : \mathbb{N}), \operatorname{h}\left(rho^{n} \times M\right) = \operatorname{h}\left(M\right))) \Rightarrow \operatorname{h}\left(M\right) = \operatorname{h}\left(0\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/GeometricScaleRigidity.geometric_scale_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The powers of rho converge to zero because rho is nonnegative and less than one. Multiplication by the fixed M preserves this limit, and continuity of h at zero sends the geometric orbit to h(0).

The orbit is also constant at h(M) by the stated hypothesis. Uniqueness of limits identifies the two values. This is the shrinking-scale step used in the Continuation XII argument; the surrounding quantum orbit, rate, and response hypotheses remain separate.

## References

- Truth anchor: `D5/S0/Asymptotics/GeometricScaleRigidity.geometric_scale_rigidity`
