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

A complete application is Simon's Section 8, Theorem 5, printed page 84: compact spatial embedding and small time translations measured in a weaker space imply compactness in the intermediate space. Let X, B and Y be real Banach spaces in independent universes, i:X->B and j:B->Y continuous injective linear maps, with i compact, and T>0. Let 1<=p<=infinity and let S be any norm-bounded, possibly empty set of actual Lp(X,p,volume restricted to Ioc(0,T)) classes. The intermediate family is S_B=i.compLpL(p,volume restricted to Ioc(0,T)) '' S.

The only time assumption is uniform positive internal translation control in Y: for each epsilon>0 there is delta>0 such that for every f in S and 0<h<min(delta,T), the Lp seminorm of t mapped to j(i(f(t+h)-f(t))) on Ioc(0,T-h) is less than epsilon. For p=infinity this is the essential-supremum seminorm. Ioc(0,T) and the open interval (0,T) have the same Lebesgue almost-everywhere classes. No values outside the original interval enter this hypothesis.

The resulting S_B has compact closure in the actual B-valued Lp space for every such p. At p=infinity there is also a map R from the original subtype S to C([0,T];B): R(f) equals i(f) almost everywhere, is the unique continuous representative on the whole closed interval, and the range of R has compact closure in the uniform norm. This is a derived application of existing formal results, with no additional retained Lean declaration or mathematical originality claim.

The spatial estimate is the general Ehrling inequality: for every a>0 there is a real C_a such that norm(i(x))<=a*norm(x)+C_a*norm(j(i(x))) for every x in X. Its authored Lean proof is due to Nickrobbins95 in prove2me/formalpedia, revision e82fff3d729d46e3ddaf6b51f4bb376b16554bae, envs/0df444a/Solutions/Sol_HunterPDE_Parabolic_ehrling.lean, Apache-2.0, SHA256 f8fa04fd3e3b739baee4f88e36e7af15f64423f95fa77d846cc8111865419ac9. The immutable supplier link is https://github.com/prove2me/formalpedia/blob/e82fff3d729d46e3ddaf6b51f4bb376b16554bae/envs/0df444a/Solutions/Sol_HunterPDE_Parabolic_ehrling.lean. Independent universes are received through the faithful external Ehrling telescope; its proof body is unchanged. No external proof code is retained here.

Choose M>0 bounding the X-valued Lp norms of S and set c=max(C_a,0). Write D_X, D_B and D_Y for the respective internal translation seminorms at a fixed f and h. Restriction and positive-translation measure preservation bound both X-valued terms by M, so D_X<=2*M. Ehrling, monotonicity, the Lp triangle inequality and homogeneity give D_B<=a*D_X+c*D_Y<=2*a*M+c*D_Y, including p=infinity. Given epsilon>0, one may take a=epsilon/(8*(M+1)) and ask for D_Y<epsilon/(2*(c+1)); the resulting bound is strictly less than epsilon. Thus the Y time assumption supplies the B time assumption uniformly over S_B.

These estimates respect actual Lp classes. Translation by h preserves Lebesgue measure and maps Ioc(0,T-h) onto Ioc(h,T), which is contained in Ioc(0,T). Both the unshifted restriction and shifted restriction therefore inherit the original norm bound. ContinuousLinearMap.coeFn_compLpL identifies the image class with t mapped to i(f(t)) only almost everywhere; transporting its exceptional null set through the shift identifies its internal difference with i(f(t+h)-f(t)) almost everywhere on Ioc(0,T-h). This restriction and transport justify applying the existing endpoints to S_B.

For finite p, the interval-integral premise of isCompact_closure_of_integrals_translations is derived rather than imposed on S. For every 0<=a<b<=T, finite-measure Lp-to-L1 comparison bounds norm(integral over Ioc(a,b) of f) by M*(b-a)^(1-1/p), uniformly in f in S, with the factor one when p=1. These Bochner integrals form a bounded subset of X. Compactness of i gives compact closure of their B images. The almost-everywhere compLpL identity and commutation of a continuous linear map with the Bochner integral identify those images with the interval-integral observations of S_B. With E=B, the existing finite-p endpoint now applies, including the first and last subintervals.

For p=infinity, apply IntervalLInfinityRepresentative.exists_continuous_representatives with E=B and family S_B to the transferred translations, and compose its representative map with f mapped to i.compLpL(f) to obtain R on S. That endpoint supplies almost-everywhere identification, a common continuity modulus and uniqueness; it alone asserts no compactness. Spatial compactness supplies the missing control of values: K=closure(i '' closedBall(0,M)) is compact in B and contains every value R(f)(t) for t in [0,T].

To prove this last containment, the essential-supremum bound gives norm(f(t))<=M almost everywhere in X, hence R(f)(t) belongs to K almost everywhere. The function t mapped to infDist(R(f)(t),K) is continuous and zero almost everywhere. Extend it by clamping t to [0,T], transfer the almost-everywhere equality from Ioc(0,T) to Icc(0,T), and use equality of continuous functions from almost-everywhere equality on a nondegenerate closed interval. It vanishes at every point, including 0 and T. Since K is closed and nonempty, zero distance gives membership in K. No pointwise X-valued lift of a continuous B-valued representative is assumed, including at the endpoints.

The common modulus and common compact value set K meet the hypotheses of pinned Mathlib's BoundedContinuousFunction.arzela_ascoli. The isometry between continuous maps on the compact interval and bounded continuous functions transfers its conclusion to compact closure of range(R) in the actual uniform norm. Finally, clamped extension followed by BoundedContinuousFunction.toLp is a continuous linear map from C([0,T];B) to the actual B-valued L-infinity space. Almost-everywhere identification sends R(f) to i.compLpL(f). Thus S_B lies in the compact image of closure(range(R)); its closed closure is compact as well.

The application uses the existing D5 finite-p compactness criterion and continuous-representative endpoint, including their private mesh, average, Fubini, almost-everywhere and endpoint constructions, without reproducing those proofs. The remaining suppliers are pinned Mathlib's eLpNorm inequalities, finite-measure comparison, translation measure preservation, Bochner integral transport, compact-operator image theorems, continuous infDist, closed-interval almost-everywhere equality, Ascoli, isometries and continuous-to-Lp maps. The Tau Ceti and uda-lab/leray-hopf contributions retain the attribution and port boundaries recorded in the literature note.

This application requires neither reflexivity, separability, finite dimensionality, time derivatives, an extra pointwise time modulus, prechosen representatives, endpoint values, boundary tails, whole-line translations nor a nonempty family. The finite-p endpoint by itself has a stronger interval-integral premise, while the representative endpoint by itself gives equicontinuity and uniqueness without compact closure. Ehrling and the compact spatial image provide exactly the additional implications needed for Simon's complete Section 8 application. The literature statement and these reused formal suppliers receive the mathematical credit; no new generality is asserted.

## References

- Truth anchor: `D5/S3/Topology/Measures/IntervalLpCompactness.isCompact_closure_of_integrals_translations`
- Truth anchor: `D5/S3/Topology/Measures/IntervalLpCompactness.mesh_error_le`
