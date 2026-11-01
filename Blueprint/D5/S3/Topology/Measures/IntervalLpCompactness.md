# Compactness from interval integrals and internal translations

## Abstract

Compact interval integrals and uniform internal positive time translations give compact closure in Banach-valued Lp.

Let E be a real Banach space, d a positive real cell width, N a natural number and f a strongly measurable E-valued function integrable on Ioc(0,N*d). The i-th cell is Ioc(i*d,(i+1)*d). Its average is the Bochner integral divided by d. The mesh function takes that average on each cell and is zero outside their union. When N is zero the interval and the union are empty.

**Theorem 1.1 (Internal shifts control the complete mesh error).**

$$\forall E \in Types,\; \forall d \in Real,\; \forall N \in Nat,\; \forall f \in Real \to E,\; \forall q \in Real,\; \left(RealBanach\left(E\right) \land \left(0 < d \land \left(StronglyMeasurable\left(f\right) \land \left(IntegrableOn\left(f, Ioc\left(0, mul\left(N, d\right)\right)\right) \land 1 \le q\right)\right)\right)\right) \Rightarrow \left(\int_{t \in Ioc\left(0, mul\left(N, d\right)\right)}\right)^{-} power\left(enorm\left(sub\left(f\left(t\right), meshAverage\left(d, N, f, t\right)\right)\right), q\right)\,dt \le mul\left(inv\left(ofReal\left(d\right)\right), mul\left(2, \left(\int_{h \in Ioc\left(0, d\right)}\right)^{-} \left(\int_{t \in Ioc\left(0, sub\left(mul\left(N, d\right), h\right)\right)}\right)^{-} power\left(enorm\left(sub\left(f\left(add\left(t, h\right)\right), f\left(t\right)\right)\right), q\right)\,dt\,dh\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/IntervalLpCompactness.mesh_error_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponent q is any real number at least one. All displayed integrals are nonnegative extended Lebesgue integrals, so the estimate remains meaningful when a power integral is infinite. No uniform norm bound on a family is used.

Hölder's inequality bounds the power error about a cell average by the reciprocal cell measure times its two-point power error. Disjoint cells make the sum of these pair integrals at most the integral over pairs in the original interval with separation at most d. Symmetry gives twice the contribution of pairs with increasing time. The measure-preserving shear (t,h) maps to (t,t+h); the resulting domain is exactly 0<h<=d and 0<t<=N*d-h. Every sampled time lies in the original interval.

The first and last cells participate in the same estimate. There is no residual boundary strip and no zero-extension translation hypothesis. The factor two is a proved convenient bound; no optimality is asserted.

**Theorem 1.2 (Compact closure in the actual Lp space).**

$$\forall E \in Types,\; \forall T \in Real,\; \forall p \in ENNReal,\; \forall S \in Set\left(Lp\left(E, p, RestrictedVolume\left(Ioc\left(0, T\right)\right)\right)\right),\; \left(RealBanach\left(E\right) \land \left(0 < T \land \left(1 \le p \land \left(p \ne \infty \land \left(\left(\forall a \in Real,\; \forall b \in Real,\; \left(0 \le a \land \left(a < b \land b \le T\right)\right) \Rightarrow IsCompact\left(closure\left(image\left(IntervalIntegral\left(a, b\right), S\right)\right)\right)\right) \land \left(\forall epsilon \in Real,\; 0 < epsilon \Rightarrow \left(\exists delta \in Real,\; 0 < delta \land \left(\forall h \in Real,\; \left(0 < h \land \left(h < delta \land h < T\right)\right) \Rightarrow \left(\forall f \in Lp\left(E, p, RestrictedVolume\left(Ioc\left(0, T\right)\right)\right),\; Member\left(f, S\right) \Rightarrow eLpNorm\left(InternalDifference\left(f, h\right), p, RestrictedVolume\left(Ioc\left(0, sub\left(T, h\right)\right)\right)\right) < ofReal\left(epsilon\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow IsCompact\left(closure\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/IntervalLpCompactness.isCompact_closure_of_integrals_translations` (`✓ std3`). ∎

*Citation.* Jacques Simon (1986). *Compact sets in the space Lp(0,T;B)*. DOI: [10.1007/BF01762360](https://doi.org/10.1007/BF01762360). URL: <https://doi.org/10.1007/BF01762360>.

*Commentary.*

E is an arbitrary real Banach space in any universe. T is positive, p is any ENNReal exponent with 1<=p and p different from infinity, and S is any subset of Lp(E,p,volume restricted to Ioc(0,T)). S may be empty. For every 0<=a<b<=T, assume compact closure in E of the image of S under its Bochner integral on Ioc(a,b). For every positive real epsilon assume a positive delta such that all f in S and all 0<h<delta with h<T have internal eLpNorm less than ofReal(epsilon). Internal means that both times t and t+h lie in the original interval, and the norm is taken over Ioc(0,T-h).

For any tolerance choose a mesh width T/N smaller than delta and T. The preceding estimate makes each function uniformly close in the actual Lp metric to its mesh average. The average coefficients belong to compact sets obtained from the compact closures of the interval-integral images by multiplication by the reciprocal cell measure. Their finite product is compact. Summing indicatorConstLp values is continuous, so the mesh averages lie in a compact subset of the same Lp space. Uniform approximation transfers total boundedness, and completeness of Lp gives compact closure.

The argument includes p=1 and infinite-dimensional targets. It adds no separate uniform Lp bound, reflexivity, separability, pointwise time modulus, continuous representative or whole-line translation hypothesis. Lebesgue AE replacement preserves both the subinterval integrals and the internal translation expression: positive translation transports null sets between the restricted intervals. The canonical representatives are used only to express these class-invariant quantities.

Simon, Section 3, Theorem 1, proves an equivalence using only strictly interior integral observations 0<a<b<T. The present endpoint-inclusive integral assumption is stronger and the conclusion is its sufficiency direction. It is not the full original equivalence. The equal-mesh estimate treats both ends simultaneously.

The scalar Hölder integral core and Banach average-power bound reuse the Tau Ceti contributors' immutable source leaves. Their attribution, hashes, license and replacement condition are recorded in the source and literature note.

## References

- Truth anchor: `D5/S3/Topology/Measures/IntervalLpCompactness.isCompact_closure_of_integrals_translations`
- Truth anchor: `D5/S3/Topology/Measures/IntervalLpCompactness.mesh_error_le`
