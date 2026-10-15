# Stopped-length continuity and deterministic depth separation

## Abstract

The complete original phase-p length law is uniformly continuous while distinct deterministic depths remain separated.

D(r) denotes the existing explicitStoppedWordLaw(p,r) pushed through lengthProjection. nativeLengthPushforward(r) is rawReadLaw(r) pushed through the actual stoppedReadWord(p) followed by lengthProjection. noncompletionMass(r) is rawReadLaw(r) of the event stoppedReadWord(p)=none. The output carrier remains Option Nat: none is infinite noncompletion, and some zero is an impossible finite length. realMass is the real value of the indicated singleton measure; mass retains its extended nonnegative real value.

For every real t and natural j, A(j) and B(j) are the polynomial coordinate extensions below. Their values at a unit-interval parameter are the complete odd and even singleton masses. coordinateDerivative(r)(j) is the sum of the two absolute derivatives, so its series includes every positive length exactly once.

$$
\forall j:Nat, (\forall t:Real, ((\operatorname{A}(j,t)=(t)*({((t)*((1-t)))}^{j}))\land (\operatorname{B}(j,t)=({((1-t))}^{2})*({((t)*((1-t)))}^{j}))))
$$

$$
\forall r:Real, (\forall j:Nat, (\operatorname{coordinateDerivative}(r,j)=(\lvert \operatorname{deriv}(\operatorname{A}(j),r)\rvert +\lvert \operatorname{deriv}(\operatorname{B}(j),r)\rvert )))
$$

TV is the existing measurableTotalVariation: the supremum of the larger of the two directed event-mass gaps over all measurable events. It takes extended nonnegative real values. ofReal embeds a real bound in that carrier. Depth is the original positive natural depth carrier, and rate(k)=fib(k+1)/fib(k+3). The addition k+1 in the display means the positive depth with that natural value; fib uses F(0)=0 and F(1)=1.

$$
\forall n:Nat, (\operatorname{adjacentLengthTV}(n)=\operatorname{TV}(\operatorname{D}(\operatorname{rate}((n+1))),\operatorname{D}(\operatorname{rate}((n+2)))))
$$

$$
\forall n:Nat, (\operatorname{adjacentFibonacciBound}(n)=\operatorname{ofReal}(\frac{12}{((7)*(\operatorname{fib}((n+4))))*(\operatorname{fib}((n+5)))}))
$$

**Theorem 1.1 (The full quantitative law).**

$$(\forall r:unitInterval, ((\operatorname{nativeLengthPushforward}(r)=\operatorname{D}(r))\land (\operatorname{noncompletionMass}(r)=0)\land (\operatorname{mass}(\operatorname{D}(r),none)=0)\land (\operatorname{mass}(\operatorname{D}(r),\operatorname{some}(0))=0)\land (\forall j:Nat, ((\operatorname{realMass}(\operatorname{D}(r),\operatorname{some}(((2)*(j)+1)))=(r)*({((r)*((1-r)))}^{j}))\land (\operatorname{realMass}(\operatorname{D}(r),\operatorname{some}(((2)*(j)+2)))=({((1-r))}^{2})*({((r)*((1-r)))}^{j}))))))\land (\forall r:Real, ((r\in [\frac{1}{3},\frac{2}{5}])\Rightarrow((\operatorname{Summable}(\operatorname{coordinateDerivative}(r)))\land ((\frac{1}{2})*(\operatorname{tsum}(\operatorname{coordinateDerivative}(r)))\le\frac{(2)*((1-r))}{(1-(r)*((1-r)))})\land (\frac{(2)*((1-r))}{(1-(r)*((1-r)))}\le\frac{12}{7}))))\land (\forall r:unitInterval, (\forall s:unitInterval, (((r\in [\frac{1}{3},\frac{2}{5}])\land (s\in [\frac{1}{3},\frac{2}{5}]))\Rightarrow(\operatorname{TV}(\operatorname{D}(r),\operatorname{D}(s))\le\operatorname{ofReal}((\frac{12}{7})*(\lvert (r-s)\rvert ))))))\land (\forall k:Depth, ((\lvert (\operatorname{rate}(k)-\operatorname{rate}((k+1)))\rvert =\frac{1}{(\operatorname{fib}((k+3)))*(\operatorname{fib}((k+4)))})\land (\operatorname{TV}(\operatorname{D}(\operatorname{rate}(k)),\operatorname{D}(\operatorname{rate}((k+1))))\le\operatorname{ofReal}(\frac{12}{((7)*(\operatorname{fib}((k+3))))*(\operatorname{fib}((k+4)))}))))\land (\operatorname{Tendsto}(adjacentFibonacciBound,atTop,\operatorname{nhds}(0)))\land (\operatorname{Tendsto}(adjacentLengthTV,atTop,\operatorname{nhds}(0)))\land (\forall k:Depth, (\forall l:Depth, ((k\neq l)\Rightarrow(\operatorname{TV}(\operatorname{dirac}(k),\operatorname{dirac}(l))=1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLengthStability.original_stopped_length_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native stopped-word theorem supplies the original parser pushforward and proves zero mass of infinite noncompletion. The existing length projection and its all-index atom identities give the two complete coordinate families; no completion conditioning or finite cutoff is used.

Differentiating each polynomial coordinate gives an absolutely summable family. The geometric series and its weighted derivative series bound half its absolute derivative sum by 2(1-r)/(1-r(1-r)), which is at most 12/7 throughout the closed interval [1/3,2/5]. The endpoint cases are included.

For ordered r at most s, the original stopped-word measures share a submeasure with odd weights r xi(r)^j and even weights (1-s)^2 xi(r)^j. Its total mass is (r+(1-s)^2)/(1-xi(r)). The event-supremum distance is at most the missing common mass, hence at most (s-r)(2-r-s)/(1-xi(r)), and therefore at most (12/7)(s-r). Symmetry covers the reverse order, including r=s, and measurable length projection contracts TV.

Vajda's Fibonacci identity gives the exact adjacent response-rate gap. The quantitative estimate applies to every positive depth; reciprocal Fibonacci products converge to zero, so the full adjacent output-law distances converge to zero. The singleton event at either of two distinct positive depths gives Dirac-law distance one.

These are different deterministic-depth sources. This result does not assert the stronger theorem about actual histories under one fixed installed prior. Exact length-law recovery is compatible with the loss of a uniform inverse stability estimate across unbounded deterministic source depths.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLengthStability.original_stopped_length_stability`
- Dependency: [D5/S1/Recurrence/FibVajda](../../../../S1/Recurrence/FibVajda.md)
- Dependency: [D5/S3/Estimation/DataProcessing/MeasurableTotalVariationTriangle](../../../Estimation/DataProcessing/MeasurableTotalVariationTriangle.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery](FourthSegmentLawRecovery.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorAbsoluteRisk](RarePriorAbsoluteRisk.md)
