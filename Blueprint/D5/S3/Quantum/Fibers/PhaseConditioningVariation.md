# Phase Variation and Positive Denominators

## Abstract

Positive probability margins bound the two symmetry-sensitive phase differences of the original five-mode transport.

The formulas use J(b) for the original open fiber. BottomMargin(b,k,e) means e<=mass(b,k,j) for every j in Fin 4. BottomProduct is the product of those four masses. WeightedIntegrable requires interval integrability of each of the five original weighted rates on [0,T]. InteriorPath and WholePathMargin impose their named conditions at every point of the closed interval. ResidualIntegral is the five component interval integral and AbsoluteRateIntegral is the integral of absolute alpha. These abbreviations retain every domain and integrability condition in the displayed statements.

**Theorem 1.1 (The sampled denominator margin).**

$$\forall b: \operatorname{Base}\left(\right), \forall k: \mathbb{R}, \forall e: \mathbb{R}, \operatorname{ValidBase}\left(b\right)\land k\in \operatorname{J}\left(b\right)\land 0<e\land \operatorname{BottomMargin}\left(b, k, e\right)\Rightarrow \operatorname{Q}\left(b, k\right)=\operatorname{I}\left(b, k\right)\operatorname{BottomProduct}\left(b, k\right)\land 4e^{3}\le\operatorname{Q}\left(b, k\right)\land 0<\operatorname{Q}\left(b, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/PhaseConditioningVariation.denominator_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base is b=(X,Y,Z), r=1-Z, with 0<Z<1 and 0<X,Y<r. The probability order is (0,1,2,3,13); index 4 denotes mode 13. At an interior height k the bottom masses are p0=r-X-Y+k, p1=X-k, p3=Y-k and p13=k. Their total is r. The information I is their reciprocal sum. Q=XY(r-X-Y)+2XYk-rk squared equals I times their product. Expanding it instead as the sum of four positive triple products proves Q positive even when r-X-Y is negative. If these four sampled masses exceed or equal epsilon>0, each triple product exceeds or equals epsilon cubed, so Q exceeds or equals four times epsilon cubed. This sampled condition does not impose a margin on intervening controls.

**Theorem 1.2 (The two pointwise estimates).**

$$\forall b: \operatorname{Base}\left(\right), \forall k: \mathbb{R}, \forall e: \mathbb{R}, \forall i: \operatorname{Fin}\left(2\right), \operatorname{ValidBase}\left(b\right)\land k\in \operatorname{J}\left(b\right)\land 0<e\land \operatorname{BottomMargin}\left(b, k, e\right)\Rightarrow \Vert\operatorname{phaseDifference}\left(\operatorname{phaseWeight}\left(b, k\right), i\right)\Vert\le\frac{\Vert\operatorname{gap}\left(b, i\right)\Vert(1-\operatorname{Z}\left(b\right))}{16e^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/PhaseConditioningVariation.pointwise_gap_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For i=0 use leftMode=1, rightMode=3 and gap=X-Y. For i=1 use leftMode=0, rightMode=4 and gap=X+Y-r. The phase weight is the original signed direction (1,-1,0,-1,1) divided by probability times I. Reciprocal subtraction gives phaseDifference(w,i)=gap/(I*pLeft*pRight). Sedrakyan's form of Cauchy-Schwarz, applied directly to the four positive masses with constant numerators one, gives I*r>=16. The two masses in the denominator each exceed or equal epsilon. Multiplying these positive inequalities yields the bound with denominator 16*epsilon squared. Both signs of either gap and both exact walls are included.

**Theorem 1.3 (The actual integral residual).**

$$\forall b: \operatorname{Base}\left(\right), \forall T: \mathbb{R}, \forall e: \mathbb{R}, \forall k: \mathbb{R}\Rightarrow \mathbb{R}, \forall a: \mathbb{R}\Rightarrow \mathbb{R}, \forall i: \operatorname{Fin}\left(2\right), \operatorname{ValidBase}\left(b\right)\land 0\le T\land 0<e\land \operatorname{IntervalIntegrable}\left(a, T\right)\land \operatorname{WeightedIntegrable}\left(b, k, a, T\right)\land \operatorname{InteriorPath}\left(b, k, T\right)\land \operatorname{WholePathMargin}\left(b, k, e, T\right)\Rightarrow \Vert\operatorname{phaseDifference}\left(\operatorname{ResidualIntegral}\left(b, k, a, T\right), i\right)\Vert\le\frac{\Vert\operatorname{gap}\left(b, i\right)\Vert(1-\operatorname{Z}\left(b\right))}{16e^{2}}\operatorname{AbsoluteRateIntegral}\left(a, T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/PhaseConditioningVariation.integral_variation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let T>=0 be finite, k(t) stay in the original open fiber, and alpha(t) be interval integrable. Assume each original component w(k(t))*alpha(t) is interval integrable and that the same epsilon>0 bounds all four bottom masses along the entire closed time interval. The residual H is their actual interval integral. Subtracting the corresponding two integrals and applying the absolute integral inequality integrates the pointwise estimate against absolute alpha. The result applies to arbitrary integrable rates, without restricting controls to finite affine menus.

For each original absolutely continuous or continuous finite-piecewise-C1 control, set alpha=deriv chi. The original control fundamental theorem supplies interval integrability and identifies its integral with chi(T)-chi(0); the original transport-integrability result supplies every weighted component. Thus Vchi is the integral of absolute deriv chi and H is the original real residual, for every signed integer winding. The two bounds are absolute(H1-H3)<=absolute(X-Y)*r*Vchi/(16*epsilon squared) and absolute(H0-H13)<=absolute(X+Y-r)*r*Vchi/(16*epsilon squared). They concern the same actual controls and the original negative state-phase convention, with the middle phase fixed.

For a nonzero target difference Delta and a nonzero corresponding gap, division by the positive r and absolute gap gives Vchi>=16*epsilon squared*absolute(Delta)/(r*absolute(gap)). On an exact wall the matching difference is zero. For a compact target difference phi in the circle of period 2*pi, every real lift x satisfies norm(phi)<=absolute(x). That quotient norm equals the distance from x to the subgroup of integer multiples of 2*pi and is independent of the selected real lift. Replacing absolute(Delta) by that invariant distance gives a necessary bound for every realization, for either coordinate pair. A wrapped representative outside the nearest fundamental interval does not supply such a bound. These are costs in phase variation and specify no calibrated energy, speed or elapsed time.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/PhaseConditioningVariation.denominator_margin`
- Truth anchor: `D5/S3/Quantum/Fibers/PhaseConditioningVariation.integral_variation_bound`
- Truth anchor: `D5/S3/Quantum/Fibers/PhaseConditioningVariation.pointwise_gap_bound`
- Dependency: [D5/S3/Quantum/Fibers/FiniteRectangleTransport](FiniteRectangleTransport.md)
