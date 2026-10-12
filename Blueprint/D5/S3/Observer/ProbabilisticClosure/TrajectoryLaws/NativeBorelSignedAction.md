# Signed acquired action and the fixed three-return estimate

## Abstract

Signed acquired action and the fixed three-return estimate.

CommonFlow contains the original two Borel probability marginals, joint flows and their Markov disintegrations, full normalized residual equations and AE complete endpoint boxes. PRealFunction means PDescriptor -> Real. Bounded(f) means measurable f with a uniform finite real norm bound. action(F,f,Q) is the Bochner integral of f against the actual weighted row F.L(Q); realIterate is its natural-number iterate. weightedNestedIntegral(F,f,Q) means integral v(W).toReal times integral f(R) dA(W) dB(Q). uReal is u.toReal. No sign restriction is placed on f in the weighted action identity.

False encodes the lower endpoint a=1/3 and true the upper endpoint b=2/5. cR is respectively 4/9 or 9/25; zR is 2/9 or 6/25; signR is +1 or -1. defect=signR(cR-g.toReal), late(j)=signR(coordinate(j,1).toReal-cR*zR^j), and variation=signR(action(F,1)-zR). mean, meanRealIterate, meanDefect and meanLate are real integrals against the original unweighted nuP. AE(mu,Q,body) binds Q almost everywhere under mu; apply denotes function application.

The public original coordinate_step and A_coordinate suppliers retain their original statements and proofs. The signed coordinate bridge converts the original ENNReal coordinate integral to a real integral after finite-measure and bounded-coordinate checks. Original unweighted marginal transport sends null inputs to null conditional rows, and L<=C then transports AE equality and order. Stationarity belongs to C=BA; L has no invariant-probability premise.

**Theorem 1.1 (The actual signed weighted action).**

$$\forall F: CommonFlow, \forall f: PRealFunction, \forall Q: PDescriptor, (\operatorname{Bounded}\left(f\right))\Rightarrow(\operatorname{action}\left(F, f, Q\right)={1-\operatorname{uReal}\left(Q\right)} \cdot {\operatorname{weightedNestedIntegral}\left(F, f, Q\right)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSignedAction.weighted_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constant-density measure scaling and the Bochner kernel composition theorem identify the actual L row with (1-u)B(vAf). Boundedness provides every required integrability premise.

**Theorem 1.2 (Unweighted integrated iterate comparison).**

$$\forall F: CommonFlow, \forall f: PRealFunction, \forall n: Nat, (\operatorname{Bounded}\left(f\right))\Rightarrow((\operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, 0\leq \operatorname{apply}\left(f, Q\right)\right))\Rightarrow(({{\frac{1}{5}}^{n}} \cdot {\operatorname{mean}\left(F, f\right)}\leq \operatorname{meanRealIterate}\left(F, f, n\right))\land(\operatorname{meanRealIterate}\left(F, f, n\right)\leq {{\frac{4}{15}}^{n}} \cdot {\operatorname{mean}\left(F, f\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSignedAction.integrated_iterate_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual row comparison (1/5)C<=L<=(4/15)C and the original C stationarity give one-step integral bounds. Positive action preserves marginal-AE nonnegativity; induction gives both powers on the same unweighted margin.

**Theorem 1.3 (The signed late predecessor controls three returns).**

$$\forall F: CommonFlow, \forall b: Bool, \forall k: Nat, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, {{\operatorname{zR}\left(b\right)}^{k+4}} \cdot {\operatorname{realIterate}\left(F, \operatorname{defect}\left(b\right), 3, Q\right)}\leq {{\operatorname{zR}\left(b\right)}^{3}} \cdot {\operatorname{apply}\left(\operatorname{late}\left(b, k+4\right), Q\right)}+{{\operatorname{zR}\left(b\right)}^{2}} \cdot {\operatorname{action}\left(F, \operatorname{late}\left(b, k+4\right), Q\right)}+{\operatorname{zR}\left(b\right)} \cdot {\operatorname{realIterate}\left(F, \operatorname{late}\left(b, k+4\right), 2, Q\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSignedAction.three_step_late_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original late marker ordering gives nonnegative late(j) only for j>=3. For n=k+4, positivity yields c*z^(k+3)*variation<=late(n), with variation still signed. Apply the actual action zero, one and two times. The exact identity L^3 defect=c(z^2 variation+z L variation+L^2 variation)-late(3) and late(3)>=0 give the displayed inequality with natural powers only.

**Theorem 1.4 (Uniform integrated three-return estimate).**

$$\forall F: CommonFlow, \forall b: Bool, \forall k: Nat, {{{\frac{1}{5}}^{3}} \cdot {{\operatorname{zR}\left(b\right)}^{k+4}}} \cdot {\operatorname{meanDefect}\left(F, b\right)}\leq {{\operatorname{zR}\left(b\right)}^{3}+{\frac{4}{15}} \cdot {{\operatorname{zR}\left(b\right)}^{2}}+{{\frac{4}{15}}^{2}} \cdot {\operatorname{zR}\left(b\right)}} \cdot {\operatorname{meanLate}\left(F, b, k+4\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSignedAction.integrated_three_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integrate the actual AE three-return inequality using bounded real functions. The lower iterate comparison is used exactly three times on defect; the upper comparison is used zero, one and two times on late(n). The resulting coefficient and (1/5)^3 do not depend on n or the Borel support.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSignedAction.integrated_iterate_bounds`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSignedAction.integrated_three_step`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSignedAction.three_step_late_bound`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSignedAction.weighted_action`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification](NativeBorelEndpointIdentification.md)
