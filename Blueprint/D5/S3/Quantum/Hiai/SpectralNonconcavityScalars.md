# Scalar dependencies of the UNTILDE proof

## Abstract

Pure real root and scale estimates supply the full UNTILDE matrix obstruction.

These are consumed helpers of SpectralNonconcavity, with their original namespace and parameters. They organize the existing proof and do not assert a separate resolution of Hiai's problem. The matrix owner retains the native geometric mean, spectral CFC powers, density paths, noncommutativity and all endpoint theorems.

For real u,v,w, radius is sqrt(((u-w)/2)^2+v^2), and lowerRoot and upperRoot are (u+w)/2 minus and plus radius. For real alpha,p, interior is min(1/4,(2^(-alpha/(1-alpha))-1/2)^(1/p)). These definitions are total; the theorems state every positivity and interval condition they use.

For real p,s, put z=scale(p,s)=s^(p/2), x=entryX(p,s)=(1-s^2)^p, a=entryA(p,s)=((1-s)^p+z^2)/2, b=entryB(p,s)=((1-s)^p-z^2)/2, e=entryE(p,s)=((1-s^2)(1-s))^(p/2), and c=entryC(p,s)=sqrt(a(x+z^4)+2z^3 e). The entry functions are u=entryU(p,s)=(a+z^3 e/x)/c, v=entryV(p,s)=b/c, w=entryW(p,s)=(a+e/z)/c, and scaledW(p,s)=(za+e)/c. The finite factors are largeScale(p,s)=upperRoot(zu,zv,scaledW), small(p,s)=e/(x largeScale), ratio(p,s)=z small/largeScale, and slope(alpha,p,s)=largeScale^(alpha-1) z^(1-alpha)(1-ratio^alpha)/(1-ratio). Finally k=sqrt(1/2). Every power in this owner is a real scalar power.

**Theorem 1.1 (Ordered roots and determinant).**

$$\forall u: \mathbb{R}, \forall v: \mathbb{R}, \forall w: \mathbb{R}, (0 < v) \Rightarrow (((0 < \operatorname{radius}\left(u, v, w\right)) \land (\operatorname{lowerRoot}\left(u, v, w\right) < \operatorname{upperRoot}\left(u, v, w\right))) \land (\operatorname{upperRoot}\left(u, v, w\right) \cdot \operatorname{lowerRoot}\left(u, v, w\right) = u \cdot w - \operatorname{rpow}\left(v, 2\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.root_algebra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positivity of the radius orders the roots; their product is uw-v squared. The matrix root_power, actual_roots and actual_power proofs consume this algebra.

**Theorem 1.2 (Positive root scaling).**

$$\forall z: \mathbb{R}, \forall u: \mathbb{R}, \forall v: \mathbb{R}, \forall w: \mathbb{R}, (0 \le z) \Rightarrow (z \cdot \operatorname{upperRoot}\left(u, v, w\right) = \operatorname{upperRoot}\left(z \cdot u, z \cdot v, z \cdot w\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.scaled_upperRoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative scaling commutes with the upper root. actual_roots uses this identity to identify the scaled eigenvalue of the actual native mean.

**Theorem 1.3 (Finite-factor spectral slope).**

$$\forall M: \mathbb{R}, \forall m: \mathbb{R}, \forall z: \mathbb{R}, \forall c: \mathbb{R}, \forall alpha: \mathbb{R}, (((((0 < M) \land (0 < m)) \land (0 < z)) \land (c = z \cdot M)) \land (m \neq M)) \Rightarrow (\frac{\operatorname{rpow}\left(M, alpha\right) - \operatorname{rpow}\left(m, alpha\right)}{M - m} = \frac{\operatorname{rpow}\left(c, alpha - 1\right) \cdot \operatorname{rpow}\left(z, 1 - alpha\right) \cdot \left(1 - \operatorname{rpow}\left(\frac{m}{M}, alpha\right)\right)}{1 - \frac{m}{M}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.slope_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact divided difference is written using finite c=zM and the ratio m/M. actual_power uses it in the true matrix spectral power.

**Theorem 1.4 (Strict scalar gap).**

$$\forall alpha: \mathbb{R}, \forall p: \mathbb{R}, (((0 < alpha) \land (alpha < \frac{1}{2})) \land (0 < p)) \Rightarrow (((0 < \operatorname{interior}\left(alpha, p\right)) \land (\operatorname{interior}\left(alpha, p\right) \le \frac{1}{4})) \land (\operatorname{rpow}\left(\frac{\operatorname{rpow}\left(1 - \operatorname{interior}\left(alpha, p\right), p\right) + \operatorname{rpow}\left(\operatorname{interior}\left(alpha, p\right), p\right)}{2}, \frac{1 - alpha}{p}\right) < \operatorname{rpow}\left(2, \frac{0 - alpha}{p}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.interior_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive p and 0<alpha<1/2, the explicit interior coordinate is positive, at most one quarter, and has the strict gap displayed here. lower_half_witness and both branches of off_midpoint_violation consume it.

**Theorem 1.5 (Square of the scale).**

$$\forall p: \mathbb{R}, \forall s: \mathbb{R}, (0 \le s) \Rightarrow (\operatorname{rpow}\left(\operatorname{scale}\left(p, s\right), 2\right) = \operatorname{rpow}\left(s, p\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.scale_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

native_two_scale uses this equality to recover the balanced matrix eigenvalues. entry_facts also consumes it.

**Theorem 1.6 (Fourth power of the scale).**

$$\forall p: \mathbb{R}, \forall s: \mathbb{R}, (0 \le s) \Rightarrow (\operatorname{rpow}\left(\operatorname{scale}\left(p, s\right), 4\right) = \operatorname{rpow}\left(\operatorname{rpow}\left(s, 2\right), p\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.scale_fourth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

native_two_scale uses this equality to recover the diagonal matrix eigenvalues.

**Theorem 1.7 (Positive entries and exact identities).**

$$\forall p: \mathbb{R}, \forall s: \mathbb{R}, (((0 < p) \land (0 < s)) \land (s < \frac{1}{2})) \Rightarrow (((((((((0 < \operatorname{scale}\left(p, s\right)) \land (0 < \operatorname{entryX}\left(p, s\right))) \land (0 < \operatorname{entryA}\left(p, s\right))) \land (0 < \operatorname{entryB}\left(p, s\right))) \land (0 < \operatorname{entryE}\left(p, s\right))) \land (0 < \operatorname{entryC}\left(p, s\right))) \land (\operatorname{rpow}\left(\operatorname{entryE}\left(p, s\right), 2\right) = \operatorname{entryX}\left(p, s\right) \cdot \operatorname{rpow}\left(1 - s, p\right))) \land (\operatorname{rpow}\left(\operatorname{entryA}\left(p, s\right), 2\right) - \operatorname{rpow}\left(\operatorname{entryB}\left(p, s\right), 2\right) = \operatorname{rpow}\left(1 - s, p\right) \cdot \operatorname{rpow}\left(\operatorname{scale}\left(p, s\right), 2\right))) \land (\operatorname{rpow}\left(\operatorname{entryC}\left(p, s\right), 2\right) = \operatorname{entryA}\left(p, s\right) \cdot \left(\operatorname{entryX}\left(p, s\right) + \operatorname{rpow}\left(\operatorname{scale}\left(p, s\right), 4\right)\right) + 2 \cdot \operatorname{rpow}\left(\operatorname{scale}\left(p, s\right), 3\right) \cdot \operatorname{entryE}\left(p, s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.entry_facts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive p and 0<s<1/2, the six scalar factors are positive, e squared equals x(1-s)^p, a squared minus b squared equals (1-s)^p z squared, and c squared has its defining radicand. native_two_scale, scaled_entries, actual_roots and actual_power consume these facts.

**Theorem 1.8 (The right-hand neighborhood).**

$$\operatorname{Eventually}\left(\operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), s \mapsto (0 < s) \land (s < \frac{1}{2})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.small_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The right-hand neighborhood of zero eventually lies in (0,1/2). fixed_diagonal_limit, two_scale_matrix_limit, two_scale_trace_limit and lower_half_witness consume the same event.

**Theorem 1.9 (Limits of finite scalar entries).**

$$\forall p: \mathbb{R}, (0 < p) \Rightarrow (((((((\operatorname{Tendsto}\left(\operatorname{scale}\left(p\right), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(0\right)\right)) \land (\operatorname{Tendsto}\left(\operatorname{entryX}\left(p\right), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(1\right)\right))) \land (\operatorname{Tendsto}\left(\operatorname{entryE}\left(p\right), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(1\right)\right))) \land (\operatorname{Tendsto}\left(\operatorname{entryC}\left(p\right), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(k\right)\right))) \land (\operatorname{Tendsto}\left(\operatorname{entryU}\left(p\right), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(k\right)\right))) \land (\operatorname{Tendsto}\left(\operatorname{entryV}\left(p\right), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(k\right)\right))) \land (\operatorname{Tendsto}\left(\operatorname{scaledW}\left(p\right), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(\frac{1}{k}\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.entry_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every p>0 as s approaches zero from the right, z tends to zero, x and e to one, c,u,v to k, and scaledW to 1/k. weightedColumns_limit consumes the result; finite_factor_limits also uses it.

**Theorem 1.10 (Limits of the scaled root and slope).**

$$\forall alpha: \mathbb{R}, \forall p: \mathbb{R}, (((0 < alpha) \land (alpha < 1)) \land (0 < p)) \Rightarrow ((((\operatorname{Tendsto}\left(\operatorname{largeScale}\left(p\right), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(\frac{1}{k}\right)\right)) \land (\operatorname{Tendsto}\left(\operatorname{small}\left(p\right), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(k\right)\right))) \land (\operatorname{Tendsto}\left(\operatorname{ratio}\left(p\right), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(0\right)\right))) \land (\operatorname{Tendsto}\left(\operatorname{slope}\left(alpha, p\right), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(0\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.finite_factor_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every 0<alpha<1 and p>0, largeScale tends to 1/k, small to k, ratio and slope to zero. weightedColumns_limit uses these finite factors; the divergent native mean is not asserted continuous.

**Theorem 1.11 (Normalization of the matrix limit).**

$$\forall alpha: \mathbb{R}, \operatorname{rpow}\left(k, alpha\right) \cdot \operatorname{rpow}\left(k, alpha\right) = \operatorname{rpow}\left(2, 0 - alpha\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.k_square_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real alpha, k^alpha k^alpha=2^(-alpha). two_scale_matrix_limit consumes this exact normalization.

## References

- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.entry_facts`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.entry_limits`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.finite_factor_limits`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.interior_gap`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.k_square_power`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.root_algebra`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.scale_fourth`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.scale_square`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.scaled_upperRoot`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.slope_factor`
- Truth anchor: `D5/S3/Quantum/Hiai/SpectralNonconcavityScalars.small_interval`
