# Spheres in additive subgroups

## Abstract

A radial obstruction to additive kernels in real inner product spaces.

**Theorem 1.1 (A sphere and its half-radius obstruction).**

$$\forall E: \operatorname{Type},\ [\operatorname{NormedAddCommGroup}\left(E\right)],\ [\operatorname{InnerProductSpace}\left(\mathbb{R}, E\right)],\ [\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)],\ K: \operatorname{AddSubgroup}\left(E\right),\ r: \mathbb{R},\ 0<r \land (\forall x: E,\ \operatorname{norm}\left(x\right)=r \Rightarrow x\in K) \land (\forall x: E,\ \operatorname{norm}\left(x\right)=\frac{r}{2} \Rightarrow \neg (x\in K)) \Rightarrow \operatorname{finrank}\left(\mathbb{R}, E\right)\le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SphericalAdditiveKernel.finrank_le_one_of_sphere_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a finite-dimensional real inner product space, K an additive subgroup of E, and r a positive real number. Suppose every vector of norm r belongs to K, and every vector of norm r/2 lies outside K. Then the real dimension of E is at most one. No continuity or closedness assumption is imposed on K.

If E had dimension at least two, choose orthonormal vectors e and f. The vectors u=(r/4)e+(sqrt(15)r/4)f and v=-(r/4)e+(sqrt(15)r/4)f both have norm r. Their difference is (r/2)e and therefore has norm r/2. Additive closure puts this difference in K, contradicting the second assumption.

For an exponential homomorphism on a commuting linear subspace, its kernel is an additive subgroup. A radial comparison formula can place the radius-r sphere in that kernel and exclude the half-radius sphere. The theorem then bounds the dimension of that particular commuting subspace; the exponential homomorphism and both radial assertions must be established for the application.

## References

- Truth anchor: `D5/S3/Geometry/SphericalAdditiveKernel.finrank_le_one_of_sphere_mem`
