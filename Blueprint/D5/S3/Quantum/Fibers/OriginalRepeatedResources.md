# Resources of the Original Repeated Controls

## Abstract

The literal repeated excursions have finite affine partitions and resources computed from their derivatives.

**Theorem 1.1 (Finite piecewise continuous rates).**

$$\forall B:Band,n:\mathbb{N},chi:\mathbb{R},1\leq n\Rightarrow \operatorname{FC1}(2,\operatorname{E}(B,n),\operatorname{const}(chi))\land \operatorname{FC1}(2,\operatorname{L}(B,n),\operatorname{const}(chi))\land (\forall e:Bool,\operatorname{IsLeast}(\operatorname{ProbRange}(B,n,e),\operatorname{min}(\operatorname{a}(B),\operatorname{min}(\operatorname{c}(B)-\operatorname{b}(B),1-2\operatorname{c}(B)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalRepeatedResources.early_late_finite_c1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Band B consists of real 0<a<b<c<1/2. For n>=1, E(B,n) and L(B,n) are exactly Band.early and Band.late. Their common prefix performs n affine excursions from a to b and back on [0,1], with half-step 1/(2*n). E has its additional excursion on [1,3/2] and then waits; L waits on [1,3/2] and performs the excursion on [3/2,2]. J(f,g,T) is f up to T and f(T)+g(t-T)-g(0) thereafter. The phase is the arbitrary real constant chi.

FC1(T,k,h) is FiniteC1Control: there exist a natural N and a monotone sequence time with time(0)=0 and time(N)=T; on every closed consecutive interval both rate functions are continuous, and on its open interior they are the actual derivatives of k and h. Each affine leg supplies its rate. Concatenation joins the finite partitions and translates the second partition and its rates. Repeating this construction gives certificates for the actual height functions, including the waiting interval. It asserts no uniform bound on the number of pieces. The support margin is also exact: ProbRange(B,n,e) is the set of all p_i(k(t)) for t in [0,2] and i in Fin5. Its least member is min(a,c-b,1-2*c), which is positive. The range bound a<=k<=b proves the lower bound. The value a occurs at t=2 in mode 0; c-b occurs at the excursion peak in mode 1; and the middle mode is always 1-2*c. The early peak is 5/4 and the late peak is 7/4.

**Theorem 1.2 (Exact coordinate length and quadratic energy).**

$$\forall B:Band,n:\mathbb{N},e:Bool,chi:\mathbb{R},1\leq n\Rightarrow \operatorname{IntervalIntegrable}(\operatorname{abs}(\operatorname{deriv}(\operatorname{If}(e,\operatorname{E}(B,n),\operatorname{L}(B,n)))),0,2)\land \operatorname{IntervalIntegrable}(\operatorname{square}(\operatorname{deriv}(\operatorname{If}(e,\operatorname{E}(B,n),\operatorname{L}(B,n)))),0,2)\land \operatorname{L}(\operatorname{If}(e,\operatorname{E}(B,n),\operatorname{L}(B,n)),\operatorname{const}(chi),2)=2\cdot (n+1)\cdot (\operatorname{b}(B)-\operatorname{a}(B))\land \operatorname{Q}(\operatorname{If}(e,\operatorname{E}(B,n),\operatorname{L}(B,n)),\operatorname{const}(chi),2)=(4n^{2}+8)\cdot {(\operatorname{b}(B)-\operatorname{a}(B))}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalRepeatedResources.early_late_integral_resources` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either actual height k and arbitrary constant real phase chi, coordinate length L is the interval integral of sqrt(deriv(k)^2+deriv(const(chi))^2), and coordinate energy Q is the interval integral of deriv(k)^2+deriv(const(chi))^2, on [0,2]. Since the phase derivative is zero these are the integrals of |deriv(k)| and deriv(k)^2. Both height integrands are interval integrable. These resources are computed from the actual piecewise functions, rather than prescribed as coefficients of a control record.

On either open side of a concatenation, its derivative is the corresponding original derivative, with the second clock translated by T. The joining singleton is Lebesgue null. Splitting interval integrals therefore adds the two actual resources. More generally the calculation applies to any real function F of the derivative, since each affine piece has constant derivative. Each prefix excursion has rates plus and minus 2*n*(b-a), each for 1/(2*n). The suffix rates are plus and minus 4*(b-a), each for 1/4, and zero for 1/2. Substituting absolute value and square gives the displayed formulas, independent of the suffix order.

The two values agree within each pair and grow with n. Constant phase contributes zero derivative energy. Metric total variation and essential speed are given below for the same functions and clock. It does not establish arbitrary-reference quantum instrument distance or its operational supremum.

**Theorem 1.3 (Metric total variation equals length).**

$$\forall B:Band,n:\mathbb{N},e:Bool,1\leq n\Rightarrow \operatorname{V}(\operatorname{If}(e,\operatorname{E}(B,n),\operatorname{L}(B,n)))=\operatorname{ofReal}(2(n+1)\cdot (\operatorname{b}(B)-\operatorname{a}(B)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalRepeatedResources.early_late_total_variation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

V(k) is eVariationOn(k,[0,2]), the supremum over ordered finite partitions of the sum of successive absolute increments, with values in the extended nonnegative reals. ofReal embeds a nonnegative real in that space. Variation adds across a joined endpoint. On each monotone affine leg it equals the absolute endpoint increment; translating the second clock preserves it. Hence each excursion contributes 2*(b-a), a waiting segment contributes zero, and the complete control has exactly n+1 excursions. Its total variation therefore equals the coordinate length computed above.

**Theorem 1.4 (Essential speeds and constant phase).**

$$\forall B:Band,n:\mathbb{N},e:Bool,chi:\mathbb{R},1\leq n\Rightarrow \operatorname{S}(\operatorname{If}(e,\operatorname{E}(B,n),\operatorname{L}(B,n)))=\operatorname{max}(2n,4)\cdot (\operatorname{b}(B)-\operatorname{a}(B))\land \operatorname{V}(\operatorname{const}(chi))=0\land \operatorname{S}(\operatorname{const}(chi))=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalRepeatedResources.early_late_essential_speed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

S(k) is the real essential supremum of |deriv(k)| for Lebesgue measure restricted to (0,2]. The derivative exists except at finitely many joining points; those points do not affect the essential supremum. The exact integral formula for an arbitrary function F of the derivative also applies to the indicator that |deriv(k)| exceeds a proposed bound. At max(2*n,4)*(b-a) its integral is zero, proving the almost-everywhere upper bound. If the essential supremum were smaller, that indicator would have positive integral on either the prefix or suffix affine pieces, contradicting its almost-everywhere vanishing. Constant phase has zero metric variation and zero essential derivative speed.

All formulas retain the original duration 2 and quantify over every n>=1. Since every resource formula is independent of the Boolean branch, the listed aggregate resources are equal within each early/late pair. Together with OriginalRepeatedMarkedLaw.marked_inverse_nonuniformity, these same pairs rule out a uniform marked-law inverse modulus even when each compared pair must have equal aggregate resources. Their common variation, length, energy and speed grow with n, so this consequence supplies no common finite speed or variation cap. The arbitrary-reference operational distance requires its own quantum-output argument.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OriginalRepeatedResources.early_late_essential_speed`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalRepeatedResources.early_late_finite_c1`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalRepeatedResources.early_late_integral_resources`
- Truth anchor: `D5/S3/Quantum/Fibers/OriginalRepeatedResources.early_late_total_variation`
- Dependency: [D5/S3/Quantum/Fibers/OriginalRepeatedMarkedLaw](OriginalRepeatedMarkedLaw.md)
