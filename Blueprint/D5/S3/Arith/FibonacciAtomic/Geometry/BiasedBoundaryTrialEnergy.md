# Stopping-Cylinder Trial Energy

## Abstract

Every function constant on an actual biased stopping partition has a finite unit-edge extension and a strict free-root Rayleigh bound.

**Theorem 1.1 (The Original Single-Edge Trial Extension).**

$$\forall t: \operatorname{Threshold}\left(\right), (\forall F: \operatorname{Vt}\left(t\right), (\exists z: \operatorname{H}\left(\right), ((z=\sum_{p\in \operatorname{A}\left(t\right)} (\operatorname{single}\left(2, p, \operatorname{atomMean}\left(p, \operatorname{val}\left(F\right)\right)\right)))\land (\operatorname{J}\left(z\right)=\operatorname{val}\left(F\right))\land ((\Vert z \Vert)^{2}=\sum_{p\in \operatorname{A}\left(t\right)} ((\operatorname{atomMean}\left(p, \operatorname{val}\left(F\right)\right))^{2}))\land (\operatorname{val}\left(F\right)\in D)\land ((\Vert \operatorname{val}\left(F\right) \Vert)^{2}=\sum_{p\in \operatorname{A}\left(t\right)} (\operatorname{measureReal}\left(M, \operatorname{cylinder}\left(\operatorname{val}\left(p\right)\right)\right)\cdot (\operatorname{atomMean}\left(p, \operatorname{val}\left(F\right)\right))^{2}))\land (\operatorname{energy}\left(\operatorname{val}\left(F\right)\right)\leq (\Vert z \Vert)^{2})\land (\operatorname{val}\left(F\right)\neq 0\implies (((b\cdot \operatorname{val}\left(t\right))\cdot (\Vert z \Vert)^{2}< (\Vert \operatorname{val}\left(F\right) \Vert)^{2})\land ((\Vert z \Vert)^{2}< (b\cdot \operatorname{val}\left(t\right))^{-1}\cdot (\Vert \operatorname{val}\left(F\right) \Vert)^{2})\land (\operatorname{energy}\left(\operatorname{val}\left(F\right)\right)< (b\cdot \operatorname{val}\left(t\right))^{-1}\cdot (\Vert \operatorname{val}\left(F\right) \Vert)^{2}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrialEnergy.actual_stopping_trial_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any real threshold t strictly between zero and one. A(t) is the first actual biased mass crossing, with equality included as a stopping event. Vt(t) is the span of its cylinder indicators in the original G=L2(M). The coefficients x(p)=atomMean(p)(F) are the actual normalized cylinder integrals of F.

The orthogonal cylinder projection fixes each F in Vt(t), so F is the sum of x(p) times its actual cylinder indicators. Put the coefficient x(p) on the single original edge p for every p in A(t), with every other edge coefficient zero and root value zero. Applying J to this finite increment sum gives F. The squared increment norm is the sum of x(p) squared.

The actual partition norm identity and its constant conditional pullbacks give the boundary squared norm as the sum of mass(p) times x(p) squared. Each actual stopping mass is strictly greater than b*t. If F is nonzero, at least one coefficient is nonzero, so the weighted sum is strictly greater than b*t times the squared increment norm.

This extension places F in the original free-root domain D. The attained original minimum energy is at most the squared norm of this extension, hence strictly less than the boundary squared norm divided by b*t for every nonzero F. Equality of the chosen extension energy with the minimum is not asserted. The statement includes zero F, with the strict conclusions restricted exactly to nonzero F.

Here J, M, D and energy are the original biased trace, measure, free-root domain and infimum over all original extensions. The same inequality therefore applies to the centered trial subspace. The polar range identifications, spectral cutoff dimensions and resulting global eigenvalue counts require their further operator and variational arguments.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrialEnergy.actual_stopping_trial_energy`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm](BiasedBoundaryFreeRootForm.md)
