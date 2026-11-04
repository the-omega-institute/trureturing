# Continuous representatives from internal L-infinity translations

## Abstract

Internal essential-supremum translations produce unique continuous representatives with a common modulus on a closed interval.

Throughout, E is a real Banach space in any universe. Ioc(a,b) is the right-closed interval (a,b], and Icc(a,b) is the closed interval [a,b]. RestrictedVolume denotes restricted Lebesgue measure. Average(f,A) is the Bochner integral of f over A divided by its measure. InternalDifference(f,h) is the function t mapped to f(t+h)-f(t). AEEq(mu,f,g) means equality of the two functions almost everywhere for mu. The projection projIcc(0,T,t) clamps t to [0,T] and takes values in that closed-interval subtype. IccExtend(g,0,T) is the real-line function t mapped to g(projIcc(0,T,t)).

**Theorem 1.1 (Consistency of arbitrary short interval averages).**

$$\forall E \in Types,\; \forall f \in Real \to E,\; \forall T \in Real,\; \forall delta \in Real,\; \forall epsilon \in Real,\; \forall a \in Real,\; \forall b \in Real,\; \forall c \in Real,\; \forall d \in Real,\; \left(RealBanach\left(E\right) \land \left(StronglyMeasurable\left(f\right) \land \left(IntegrableOn\left(f, Ioc\left(0, T\right)\right) \land \left(0 \le epsilon \land \left(\left(\forall h \in Real,\; \left(0 < h \land \left(h < delta \land h < T\right)\right) \Rightarrow eLpNorm\left(InternalDifference\left(f, h\right), \infty, RestrictedVolume\left(Ioc\left(0, sub\left(T, h\right)\right)\right)\right) < ofReal\left(epsilon\right)\right) \land \left(0 \le a \land \left(a < b \land \left(b \le T \land \left(0 \le c \land \left(c < d \land \left(d \le T \land \left(\forall x \in Real,\; \forall y \in Real,\; \left(Member\left(x, Ioc\left(a, b\right)\right) \land Member\left(y, Ioc\left(c, d\right)\right)\right) \Rightarrow abs\left(sub\left(y, x\right)\right) < delta\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow dist\left(Average\left(f, Ioc\left(a, b\right)\right), Average\left(f, Ioc\left(c, d\right)\right)\right) \le epsilon$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/IntervalLInfinityRepresentative.local_average_consistency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be strongly measurable on the real line and integrable on Ioc(0,T). Suppose every positive internal translation below delta has L-infinity seminorm less than ofReal(epsilon), where epsilon is nonnegative. Consider any two positive-length interval windows Ioc(a,b) and Ioc(c,d) contained in Ioc(0,T). If every point of one window has distance less than delta from every point of the other, then the distance of their averages is at most epsilon. The windows may have different lengths, overlap, or meet either endpoint of the original interval.

For each fixed shift the essential-supremum estimate holds outside a null set. Fubini's theorem and the measure-preserving shear (x,h) mapped to (x,x+h) give the corresponding estimate for almost every pair of times. Symmetry covers negative separations, and the diagonal has zero difference. Restricting that pair estimate to the product of the two windows and applying Mathlib's convex-set average theorem twice proves the average estimate. There is no intersection over uncountably many shift-dependent sets.

**Theorem 1.2 (A common modulus for the unique continuous representatives).**

$$\forall E \in Types,\; \forall T \in Real,\; \forall S \in Set\left(Lp\left(E, \infty, RestrictedVolume\left(Ioc\left(0, T\right)\right)\right)\right),\; \left(RealBanach\left(E\right) \land \left(0 < T \land \left(\forall epsilon \in Real,\; 0 < epsilon \Rightarrow \left(\exists delta \in Real,\; 0 < delta \land \left(\forall f \in Lp\left(E, \infty, RestrictedVolume\left(Ioc\left(0, T\right)\right)\right),\; Member\left(f, S\right) \Rightarrow \left(\forall h \in Real,\; \left(0 < h \land \left(h < delta \land h < T\right)\right) \Rightarrow eLpNorm\left(InternalDifference\left(f, h\right), \infty, RestrictedVolume\left(Ioc\left(0, sub\left(T, h\right)\right)\right)\right) < ofReal\left(epsilon\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists R \in S \to ContinuousMap\left(Icc\left(0, T\right), E\right),\; \left(\forall f \in S,\; AEEq\left(RestrictedVolume\left(Ioc\left(0, T\right)\right), IccExtend\left(R\left(f\right), 0, T\right), f\right)\right) \land \left(\left(\forall epsilon \in Real,\; 0 < epsilon \Rightarrow \left(\exists eta \in Real,\; 0 < eta \land \left(\forall f \in S,\; \forall x \in Icc\left(0, T\right),\; \forall y \in Icc\left(0, T\right),\; dist\left(x, y\right) < eta \Rightarrow dist\left(R\left(f, x\right), R\left(f, y\right)\right) < epsilon\right)\right)\right) \land \left(\left(\forall f \in S,\; \forall g \in ContinuousMap\left(Icc\left(0, T\right), E\right),\; AEEq\left(RestrictedVolume\left(Ioc\left(0, T\right)\right), IccExtend\left(g, 0, T\right), f\right) \Rightarrow g = R\left(f\right)\right) \land \left(\forall f \in S,\; \forall u \in Real \to E,\; AEEq\left(RestrictedVolume\left(Ioc\left(0, T\right)\right), u, f\right) \Rightarrow \left(AEEq\left(RestrictedVolume\left(Ioc\left(0, T\right)\right), IccExtend\left(R\left(f\right), 0, T\right), u\right) \land \left(\forall h \in Real,\; \left(0 < h \land h < T\right) \Rightarrow eLpNorm\left(InternalDifference\left(u, h\right), \infty, RestrictedVolume\left(Ioc\left(0, sub\left(T, h\right)\right)\right)\right) = eLpNorm\left(InternalDifference\left(f, h\right), \infty, RestrictedVolume\left(Ioc\left(0, sub\left(T, h\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/IntervalLInfinityRepresentative.exists_continuous_representatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

T is positive and S is an arbitrary, possibly empty subset of the actual Lp(E,infinity,RestrictedVolume(Ioc(0,T))) space. The translation scale is uniform over S. The map R has domain S itself and codomain the continuous maps on Icc(0,T). The first conclusion identifies each original almost-everywhere class. The second gives one epsilon-delta continuity condition for all members and all pairs of points, including 0 and T. The third gives uniqueness among all continuous representatives. The fourth permits every almost-everywhere equal real-line representative u, preserving both its identification with R(f) and every positive internal translation seminorm.

For x in [0,T] and r>0, take the average over Ioc(max(0,x-r),min(T,x+r)). This window has positive length even at x=0 or x=T. With r=1/(n+1), the consistency estimate makes these averages Cauchy. Completeness of E gives a limit at every x. The same estimate for windows centered at nearby points passes to the limits and supplies a common continuity modulus. For each of the countably many accuracies 1/(k+1), the pair estimate also makes the shrinking averages close to f(x) for almost every x. Passing to their limits identifies the continuous function with the original class. Full support of Lebesgue measure on the interval and continuity then give uniqueness.

There is no separate common bound on the norms of S, no restriction on the dimension of E, and no separability or reflexivity assumption. The integral construction uses only the individual integrability inherited from L-infinity on a finite interval. It assumes no pointwise time modulus, continuous representative, endpoint value, boundary-tail condition, or whole-line translation estimate. In particular the unbounded family of all scalar constant functions satisfies the translation condition and has a common continuity modulus; this assertion does not claim that such a family is compact.

Simon, Compact sets in the space Lp(0,T;B), DOI 10.1007/BF01762360, Section 3, Theorem 1, includes a compactness conclusion in C(0,T;B) for p=infinity and uses right means and opposite time directions. Its C convention uses the closed interval. That source does not separately state the entire arbitrary-family lifting and uniqueness assertion displayed here. The present local-window construction is a derived argument; no originality or open-problem claim is made.

## References

- Truth anchor: `D5/S3/Topology/Measures/IntervalLInfinityRepresentative.exists_continuous_representatives`
- Truth anchor: `D5/S3/Topology/Measures/IntervalLInfinityRepresentative.local_average_consistency`
