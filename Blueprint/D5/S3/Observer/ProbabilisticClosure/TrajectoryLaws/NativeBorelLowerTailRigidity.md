# Exact recurrence rigidity on the full descriptor spaces

## Abstract

Borel endpoint recurrence and the original full flows

F is the original boxed Borel CommonFlow. Its two marginals are probability measures on regular full legal-tail descriptors; GammaB and GammaA are its given directional joint measures, with their given conditional kernels B and A. Both normalized residual equations and both complete endpoint boxes are part of CommonFlow. The full legal carriers include the infinite noncompletion outcome. No atomicity, finite support, midpoint mean, loss budget or deterministic successor condition is added.

The lower native endpoint is a=1/3 and the upper endpoint is b=2/5. Their return rates are za=2/9 and zb=6/25; their marker-one coefficients are 4/9 and 9/25. nativeEndpoint(p,false) and nativeEndpoint(beta,false) are the lower full laws, and true selects the upper full laws. meanCoordinate(F,n) denotes the integral of the real marker-one coordinate at depth n against the original nuP. AE(mu,Q,P) means P holds mu-almost everywhere. cond(mu,S) is normalized restriction to S; mass(mu,x) evaluates the singleton {x}. All measure coefficients in the excision and decomposition formulas belong to ENNReal, and ofReal converts the final real weights.

**Theorem 1.1 (iterate sub).**

$$\forall F: CommonFlow, \forall f: \operatorname{Map}\left(PDescriptor, Real\right), \forall h: \operatorname{Map}\left(PDescriptor, Real\right), \forall n: Nat, ((\operatorname{Bounded}\left(f\right))\land (\operatorname{Bounded}\left(h\right)))\Rightarrow (\operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{realIterate}\left(F, \operatorname{subtractFunctions}\left(f, h\right), n, Q\right)={\operatorname{realIterate}\left(F, f, n, Q\right)}-{\operatorname{realIterate}\left(F, h, n, Q\right)}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.iterate_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

subtractFunctions(f,h)(Q)=f(Q)-h(Q). The bounded real return action preserves subtraction. Its almost-everywhere congruence propagates the identity through each finite iterate.

**Theorem 1.2 (coordinate iterates).**

$$\forall F: CommonFlow, \forall k: Nat, \forall n: Nat, \forall i: Letter, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{toReal}\left(\operatorname{coordinate}\left({k}+{n}, i, Q\right)\right)=\operatorname{realIterate}\left(F, \operatorname{realCoordinateFunction}\left(k, i\right), n, Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.coordinate_iterates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

realCoordinateFunction(k,i)(Q)=toReal(coordinate(k,i,Q)); realIterate(F,f,n,Q) evaluates the nth bounded real action iterate. The original full residual equations identify coordinate(k+n,i) with this iterate, for either letter.

**Definition 1.3 (lowerGap).**

$$\forall Q: PDescriptor, \operatorname{lowerGap}\left(Q\right)={\operatorname{toReal}\left(\operatorname{coordinate}\left(3, 1, Q\right)\right)}-{{\frac{2}{9}}^{3} \cdot \operatorname{toReal}\left(\operatorname{g}\left(Q\right)\right)}$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.lowerGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The third-return lower gap compares the full depth-three marker-one mass with za cubed times the initial marker-one mass.

**Theorem 1.4 (bounded lowerGap).**

$$\operatorname{Bounded}\left(lowerGap\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.bounded_lowerGap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each real coordinate is measurable and bounded between zero and one, so their indicated linear combination is a bounded measurable real function.

**Theorem 1.5 (lowerGap bound).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, (0\leq \operatorname{lowerGap}\left(Q\right))\land ({\frac{2}{9}}^{3} \cdot \operatorname{defect}\left(false, Q\right)\leq \operatorname{lowerGap}\left(Q\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.lowerGap_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower depth-three box gives L cubed g at least (4/9)za cubed. The original regular emission bound gives g at most 4/9. Thus the gap dominates za cubed times defect(false,Q)=4/9-toReal(g(Q)), which is nonnegative.

**Theorem 1.6 (lowerGap iterates).**

$$\forall F: CommonFlow, \forall n: Nat, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{realIterate}\left(F, lowerGap, n, Q\right)={\operatorname{toReal}\left(\operatorname{coordinate}\left({n}+{3}, 1, Q\right)\right)}-{{\frac{2}{9}}^{3} \cdot \operatorname{toReal}\left(\operatorname{coordinate}\left(n, 1, Q\right)\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.lowerGap_iterates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtraction, scalar multiplication and the full coordinate recursion express every iterate of the gap by the two original marker-one coordinates.

**Theorem 1.7 (lower completion).**

$$\forall F: CommonFlow, \forall n: Nat, (\operatorname{meanCoordinate}\left(F, {n}+{3}\right)={\frac{2}{9}}^{3} \cdot \operatorname{meanCoordinate}\left(F, n\right))\Rightarrow (\operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{toReal}\left(\operatorname{g}\left(Q\right)\right)=\frac{4}{9}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.lower_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mean equality makes the integral of L to the nth power of the gap zero. The integrated iterate bound is at least (1/5) to the nth power times the integral of the nonnegative gap. Hence the gap vanishes almost everywhere, and its positive multiple of the completion defect also vanishes. This identifies g=4/9 at the original marginal.

**Theorem 1.8 (lower native flow).**

$$\forall F: CommonFlow, \forall n: Nat, (\operatorname{meanCoordinate}\left(F, {n}+{3}\right)={\frac{2}{9}}^{3} \cdot \operatorname{meanCoordinate}\left(F, n\right))\Rightarrow ((\operatorname{nuP}\left(F\right)=\operatorname{dirac}\left(\operatorname{nativeEndpoint}\left(p, false\right)\right))\land ((\operatorname{nuB}\left(F\right)=\operatorname{dirac}\left(\operatorname{nativeEndpoint}\left(beta, false\right)\right))\land ((\operatorname{GammaB}\left(F\right)=\operatorname{dirac}\left((\operatorname{nativeEndpoint}\left(p, false\right), \operatorname{nativeEndpoint}\left(beta, false\right))\right))\land (\operatorname{GammaA}\left(F\right)=\operatorname{dirac}\left((\operatorname{nativeEndpoint}\left(beta, false\right), \operatorname{nativeEndpoint}\left(p, false\right))\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.lower_native_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The completion identity makes the lower defect integral zero. The complete measurable-event total variation estimates force zero full-law loss in both phases. Directed event bounds and measure extensionality identify each entire descriptor, including infinity. The two actual joint measures then have both coordinates fixed by their original marginals, giving the two indicated unit flows.

**Theorem 1.9 (upper native successors).**

$$\forall F: CommonFlow, (\operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, (Q=\operatorname{nativeEndpoint}\left(p, true\right))\Rightarrow (\operatorname{AE}\left(\operatorname{B}\left(F, Q\right), W, W=\operatorname{nativeEndpoint}\left(beta, true\right)\right))\right))\land (\operatorname{AE}\left(\operatorname{nuB}\left(F\right), W, (W=\operatorname{nativeEndpoint}\left(beta, true\right))\Rightarrow (\operatorname{AE}\left(\operatorname{A}\left(F, W\right), Q, Q=\operatorname{nativeEndpoint}\left(p, true\right)\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.upper_native_successors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper endpoint limit and surviving-transition theorem identify the actual B successor of an upper native p descriptor. On an upper beta descriptor, the original A barycentre is the upper p law. The endpoint event is extremal in its full box, so its nonnegative complete-law loss has zero integral; almost every actual A successor is therefore the entire upper p descriptor.

**Theorem 1.10 (upper native edges).**

$$\forall F: CommonFlow, (\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(p, true\right)\right)=\operatorname{mass}\left(\operatorname{nuB}\left(F\right), \operatorname{nativeEndpoint}\left(beta, true\right)\right))\land ((\operatorname{AE}\left(\operatorname{GammaB}\left(F\right), x, \operatorname{fst}\left(x\right)=\operatorname{nativeEndpoint}\left(p, true\right)\Leftrightarrow \operatorname{snd}\left(x\right)=\operatorname{nativeEndpoint}\left(beta, true\right)\right))\land (\operatorname{AE}\left(\operatorname{GammaA}\left(F\right), x, \operatorname{fst}\left(x\right)=\operatorname{nativeEndpoint}\left(beta, true\right)\Leftrightarrow \operatorname{snd}\left(x\right)=\operatorname{nativeEndpoint}\left(p, true\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.upper_native_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Outgoing absorption in the two directions yields opposite inequalities between the upper singleton masses. They are equal. The corresponding equal-mass event inclusions imply almost-everywhere equivalence of the two endpoint events in each actual directional joint, excluding all incoming and outgoing complement edges.

**Theorem 1.11 (upper excision).**

$$\forall F: CommonFlow, (\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(p, true\right)\right)< 1)\Rightarrow (\exists R: CommonFlow, (\operatorname{nuP}\left(R\right)=\operatorname{cond}\left(\operatorname{nuP}\left(F\right), \operatorname{complement}\left(\operatorname{singleton}\left(\operatorname{nativeEndpoint}\left(p, true\right)\right)\right)\right))\land ((\operatorname{nuB}\left(R\right)=\operatorname{cond}\left(\operatorname{nuB}\left(F\right), \operatorname{complement}\left(\operatorname{singleton}\left(\operatorname{nativeEndpoint}\left(beta, true\right)\right)\right)\right))\land ((\operatorname{GammaB}\left(R\right)=\operatorname{smul}\left(\operatorname{inverse}\left({1}-{\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(p, true\right)\right)}\right), \operatorname{restrict}\left(\operatorname{GammaB}\left(F\right), \operatorname{complement}\left(\operatorname{preimage}\left(fst, \operatorname{singleton}\left(\operatorname{nativeEndpoint}\left(p, true\right)\right)\right)\right)\right)\right))\land ((\operatorname{GammaA}\left(R\right)=\operatorname{smul}\left(\operatorname{inverse}\left({1}-{\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(p, true\right)\right)}\right), \operatorname{restrict}\left(\operatorname{GammaA}\left(F\right), \operatorname{complement}\left(\operatorname{preimage}\left(fst, \operatorname{singleton}\left(\operatorname{nativeEndpoint}\left(beta, true\right)\right)\right)\right)\right)\right))\land ((\operatorname{B}\left(R\right)=\operatorname{B}\left(F\right))\land (\operatorname{A}\left(R\right)=\operatorname{A}\left(F\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.upper_excision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalize the original marginal restrictions off the upper native singletons by the common positive mass 1-m. Restrict the actual joints by their first-coordinate complement and scale by the same reciprocal. The no-edge equivalences identify the second marginals. Absolute continuity preserves both complete boxes and normalized full residual equations. The resulting CommonFlow uses exactly the original B and A kernels on the same ambient spaces.

**Theorem 1.12 (upper complement decomposition).**

$$\forall F: CommonFlow, (\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(p, true\right)\right)< 1)\Rightarrow (\exists R: CommonFlow, (\operatorname{mass}\left(\operatorname{nuP}\left(R\right), \operatorname{nativeEndpoint}\left(p, true\right)\right)=0)\land ((\operatorname{nuP}\left(F\right)={\operatorname{smul}\left({1}-{\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(p, true\right)\right)}, \operatorname{nuP}\left(R\right)\right)}+{\operatorname{smul}\left(\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(p, true\right)\right), \operatorname{dirac}\left(\operatorname{nativeEndpoint}\left(p, true\right)\right)\right)})\land ((\operatorname{nuB}\left(F\right)={\operatorname{smul}\left({1}-{\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(p, true\right)\right)}, \operatorname{nuB}\left(R\right)\right)}+{\operatorname{smul}\left(\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(p, true\right)\right), \operatorname{dirac}\left(\operatorname{nativeEndpoint}\left(beta, true\right)\right)\right)})\land ((\operatorname{GammaB}\left(F\right)={\operatorname{smul}\left({1}-{\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(p, true\right)\right)}, \operatorname{GammaB}\left(R\right)\right)}+{\operatorname{smul}\left(\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(p, true\right)\right), \operatorname{dirac}\left((\operatorname{nativeEndpoint}\left(p, true\right), \operatorname{nativeEndpoint}\left(beta, true\right))\right)\right)})\land (\operatorname{GammaA}\left(F\right)={\operatorname{smul}\left({1}-{\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(p, true\right)\right)}, \operatorname{GammaA}\left(R\right)\right)}+{\operatorname{smul}\left(\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{nativeEndpoint}\left(p, true\right)\right), \operatorname{dirac}\left((\operatorname{nativeEndpoint}\left(beta, true\right), \operatorname{nativeEndpoint}\left(p, true\right))\right)\right)})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.upper_complement_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same remainder has zero upper singleton mass. Splitting each original measure into its singleton part and complement gives all four exact decompositions with the same upper coefficient m. In each joint, the singleton event is the matching native endpoint pair.

**Theorem 1.13 (recurrence native flow).**

$$\forall F: CommonFlow, \forall N: Nat, (\forall n: Nat, (N\leq n)\Rightarrow ({{\operatorname{meanCoordinate}\left(F, {n}+{2}\right)}-{({\frac{2}{9}}+{\frac{6}{25}}) \cdot \operatorname{meanCoordinate}\left(F, {n}+{1}\right)}}+{\frac{2}{9} \cdot \frac{6}{25} \cdot \operatorname{meanCoordinate}\left(F, n\right)}=0))\Rightarrow (\exists theta: Real, (0\leq theta)\land ((theta\leq 1)\land ((\operatorname{nuP}\left(F\right)={\operatorname{smul}\left(\operatorname{ofReal}\left({1}-{theta}\right), \operatorname{dirac}\left(\operatorname{nativeEndpoint}\left(p, false\right)\right)\right)}+{\operatorname{smul}\left(\operatorname{ofReal}\left(theta\right), \operatorname{dirac}\left(\operatorname{nativeEndpoint}\left(p, true\right)\right)\right)})\land ((\operatorname{nuB}\left(F\right)={\operatorname{smul}\left(\operatorname{ofReal}\left({1}-{theta}\right), \operatorname{dirac}\left(\operatorname{nativeEndpoint}\left(beta, false\right)\right)\right)}+{\operatorname{smul}\left(\operatorname{ofReal}\left(theta\right), \operatorname{dirac}\left(\operatorname{nativeEndpoint}\left(beta, true\right)\right)\right)})\land ((\operatorname{GammaB}\left(F\right)={\operatorname{smul}\left(\operatorname{ofReal}\left({1}-{theta}\right), \operatorname{dirac}\left((\operatorname{nativeEndpoint}\left(p, false\right), \operatorname{nativeEndpoint}\left(beta, false\right))\right)\right)}+{\operatorname{smul}\left(\operatorname{ofReal}\left(theta\right), \operatorname{dirac}\left((\operatorname{nativeEndpoint}\left(p, true\right), \operatorname{nativeEndpoint}\left(beta, true\right))\right)\right)})\land (\operatorname{GammaA}\left(F\right)={\operatorname{smul}\left(\operatorname{ofReal}\left({1}-{theta}\right), \operatorname{dirac}\left((\operatorname{nativeEndpoint}\left(beta, false\right), \operatorname{nativeEndpoint}\left(p, false\right))\right)\right)}+{\operatorname{smul}\left(\operatorname{ofReal}\left(theta\right), \operatorname{dirac}\left((\operatorname{nativeEndpoint}\left(beta, true\right), \operatorname{nativeEndpoint}\left(p, true\right))\right)\right)}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.recurrence_native_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m be the original upper native singleton mass. If m=1, absorption exhausts both original marginals and joints. Otherwise the same-kernel complement has zero upper mass and inherits the exact recurrence after subtracting the upper geometric sequence. Its normalized mean d(n)/zb to the nth power tends to zero. The scaled first difference (d(n+1)-za*d(n))/zb to the nth power is constant on the recurrence tail and tends to zero, so the remainder obeys the lower three-return equality. Lower native completion identifies all four remainder measures. Restoring the two original upper unit subflows gives the displayed formulas with theta=toReal(m), including theta=0 and theta=1. The recurrence is an added exact eventual assumption; the conclusion determines all earlier complete words and the given full directional measures.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.bounded_lowerGap`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.coordinate_iterates`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.iterate_sub`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.lowerGap`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.lowerGap_bound`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.lowerGap_iterates`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.lower_completion`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.lower_native_flow`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.recurrence_native_flow`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.upper_complement_decomposition`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.upper_excision`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.upper_native_edges`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity.upper_native_successors`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStabilityConsumers](NativeBorelStabilityConsumers.md)
