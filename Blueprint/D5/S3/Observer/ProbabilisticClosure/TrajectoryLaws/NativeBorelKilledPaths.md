# A Markov cemetery extension

## Abstract

Killed Doob paths on the original flow

**Theorem 1.1 (The extension is Markov).**

$$\forall K: \operatorname{Kernel}\left(PDescriptor, PDescriptor\right), \operatorname{Subprobability}\left(K\right)\Rightarrow\operatorname{IsMarkovKernel}\left(\operatorname{cemetery}\left(K\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.cemetery_markov` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every substochastic row is extended by its missing mass at the absorbing cemetery point, so the extended row has mass one.

**Theorem 1.2 (The original initial law).**

$$\forall S: Type, [\operatorname{MeasurableSpace}\left(S\right)] \forall mu: \operatorname{Measure}\left(S\right), \forall K: \operatorname{Kernel}\left(S, S\right), [\operatorname{IsMarkovKernel}\left(K\right)] \operatorname{map}\left(\operatorname{homogeneousLaw}\left(mu, K\right), \operatorname{eval}\left(0\right)\right)=mu$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.homogeneous_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

homogeneousStep(K,n) applies K to the last state of the complete history through n. homogeneousLaw(mu,K) is its Ionescu-Tulcea trajectory law; its time-zero marginal is exactly mu, including initial measures that are not probabilities.

**Theorem 1.3 (Mapping a density evaluated at the image).**

$$\forall S: Type, \forall U: Type, [\operatorname{MeasurableSpace}\left(S\right)] [\operatorname{MeasurableSpace}\left(U\right)] \forall mu: \operatorname{Measure}\left(S\right), \forall f: \operatorname{Function}\left(S, U\right), \operatorname{Measurable}\left(f\right)\Rightarrow\forall w: \operatorname{Function}\left(U, ENNReal\right), \operatorname{Measurable}\left(w\right)\Rightarrow\operatorname{map}\left(\operatorname{withDensity}\left(mu, \operatorname{compose}\left(w, f\right)\right), f\right)=\operatorname{withDensity}\left(\operatorname{map}\left(mu, f\right), w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.map_terminal_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary measurable spaces, measurable f and nonnegative measurable w, weighting mu by w(f(x)) and then mapping by f gives the image measure weighted by w. The finite product proof uses this identity for the complete prefix extension map.

F is the original boxed Borel CommonFlow and G is an earned measurable conull absorbing carrier. Write h=threeStepAverage and T=L/(6/25). On G, doob(F,G) has density h(R)/(h(Q)*(6/25)) with respect to the actual L row; it is the zero row outside G. Subprobability(M) means every M row has mass at most one. Cemetery is the disjoint union of the original descriptor space and one absorbing state. The extension sends each live row through the inclusion and sends its missing mass to that state. killedTrajectory is its full Ionescu-Tulcea law with initial law nuP mapped through the inclusion. It is formed from the Markov extension, while M remains substochastic.

**Theorem 1.4 (Finite conjugacy and limiting survival).**

$$\forall F: CommonFlow, \exists G\subset PDescriptor, \exists hsub: \operatorname{Subprobability}\left(\operatorname{doob}\left(F, G\right)\right), \operatorname{MeasurableSet}\left(G\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, Q\in G\right)\land \operatorname{IsMarkovKernel}\left(\operatorname{cemetery}\left(\operatorname{doob}\left(F, G\right)\right)\right)\land \operatorname{IsProbabilityMeasure}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right)\right)\land (\forall Q: PDescriptor, \operatorname{AbsolutelyContinuous}\left(\operatorname{row}\left(\operatorname{doob}\left(F, G\right), Q\right), \operatorname{CRow}\left(F, Q\right)\right))\land (\forall Q\in G, \operatorname{CoreAt}\left(F, Q\right)\land \operatorname{AE}\left(\operatorname{CRow}\left(F, Q\right), R, R\in G\right))\land (\forall phi: \operatorname{Function}\left(PDescriptor, ENNReal\right), \operatorname{Measurable}\left(phi\right)\Rightarrow\forall n: Nat, \forall Q\in G, \operatorname{normalizedIterate}\left(F, \operatorname{productFunction}\left(\operatorname{threeStepAverage}\left(F\right), phi\right), n, Q\right)=\operatorname{threeStepAverage}\left(F, Q\right) \cdot \operatorname{iterate}\left(\operatorname{doob}\left(F, G\right), phi, n, Q\right))\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{Antitone}\left(\operatorname{sequence}\left(n, \operatorname{iterate}\left(\operatorname{doob}\left(F, G\right), \operatorname{one}\left(\right), n, Q\right)\right)\right)\land \operatorname{Tendsto}\left(\operatorname{sequence}\left(n, \operatorname{iterate}\left(\operatorname{doob}\left(F, G\right), \operatorname{one}\left(\right), n, Q\right)\right), atTop, \operatorname{nhds}\left(\frac{\operatorname{q}\left(F, Q\right)}{\operatorname{threeStepAverage}\left(F, Q\right)}\right)\right)\right)\land (\forall Q\in G, 0<\operatorname{mass}\left(\operatorname{doob}\left(F, G\right), Q, \operatorname{univ}\left(\right)\right))\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{toReal}\left(1-\operatorname{mass}\left(\operatorname{doob}\left(F, G\right), Q, \operatorname{univ}\left(\right)\right)\right)=\frac{\operatorname{delta}\left(F, Q\right)}{\operatorname{h}\left(F, Q\right)}\land \frac{2}{3} \cdot \operatorname{excess}\left(Q\right)\le\operatorname{toReal}\left(1-\operatorname{mass}\left(\operatorname{doob}\left(F, G\right), Q, \operatorname{univ}\left(\right)\right)\right)\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{smul}\left({\operatorname{endpointRate}\left(\right)}^{-1}, \operatorname{LRow}\left(F, Q\right)\right)\le\operatorname{smul}\left(\operatorname{ofReal}\left(1+\frac{25 \cdot \operatorname{excess}\left(Q\right)}{9}\right), \operatorname{CRow}\left(F, Q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.common_flow_doob_survival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative measurable test phi, multiplying the M iterate by h gives the normalized L iterate of h*phi on G. This is proved at every finite depth using absorption and cancellation of the positive finite h factors. With phi=1, M^n1 decreases to q/h. The cemetery extension is a probability kernel and therefore supplies a full trajectory probability measure. Its construction and the finite conjugacy are distinct from an identity for the immortal restriction of that measure.

Every live row has positive mass, using L>=(1/5)C and the core lower bound h>=3/25. Almost everywhere the killing probability is delta/h and is at least (2/3)*excess, since delta>=excess/3 and h<=1/2. The same original completion coordinate supplies T<=(1+25*excess/9)C. These two bounds use the same acquired flow and the same excess.

**Theorem 1.5 (Probability of surviving forever).**

$$\forall F: CommonFlow, \exists G\subset PDescriptor, \exists hsub: \operatorname{Subprobability}\left(\operatorname{doob}\left(F, G\right)\right), \operatorname{MeasurableSet}\left(G\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, Q\in G\right)\land (\forall Q\in G, \forall n: Nat, 0<\operatorname{iterate}\left(\operatorname{doob}\left(F, G\right), \operatorname{one}\left(\right), n, Q\right))\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{mass}\left(\operatorname{startedTrajectory}\left(\operatorname{doob}\left(F, G\right), hsub, Q\right), \operatorname{immortal}\left(\right)\right)=\frac{\operatorname{q}\left(F, Q\right)}{\operatorname{threeStepAverage}\left(F, Q\right)}\land \operatorname{mass}\left(\operatorname{startedTrajectory}\left(\operatorname{doob}\left(F, G\right), hsub, Q\right), \operatorname{immortal}\left(\right)\right)=\operatorname{If}\left(Q=\operatorname{nativeEndpoint}\left(p, \operatorname{true}\left(\right)\right), 1, 0\right)\right)\land \operatorname{mass}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right), \operatorname{immortal}\left(\right)\right)=\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{singleton}\left(\operatorname{nativeEndpoint}\left(p, \operatorname{true}\left(\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.common_flow_immortal_survival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

immortal is the measurable event that no coordinate equals the cemetery state. startedTrajectory is the lawful cemetery process from the specified original descriptor. Its finite-time live probability is M^n1, and every finite iterate is strictly positive on G. This follows by induction from positive row mass and absorption of the same carrier. The absorbing cemetery makes the finite live events decrease almost everywhere, so continuity from above identifies the immortal probability with their infimum. The earned limit q/h therefore supplies the actual infinite-event probability almost everywhere under the original margin, including zero native mass. Integrating that probability gives precisely the upper native singleton mass. Positive finite survival is compatible with zero immortal mass.

**Theorem 1.6 (The complete immortal path measure).**

$$\forall F: CommonFlow, \exists G\subset PDescriptor, \exists hsub: \operatorname{Subprobability}\left(\operatorname{doob}\left(F, G\right)\right), \operatorname{MeasurableSet}\left(G\right)\land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, Q\in G\right)\land (\forall Q\in G, \forall n: Nat, 0<\operatorname{iterate}\left(\operatorname{doob}\left(F, G\right), \operatorname{one}\left(\right), n, Q\right))\land \operatorname{restrict}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right), \operatorname{immortal}\left(\right)\right)=\operatorname{smul}\left(\operatorname{mass}\left(\operatorname{nuP}\left(F\right), \operatorname{singleton}\left(\operatorname{nativeEndpoint}\left(p, \operatorname{true}\left(\right)\right)\right)\right), \operatorname{dirac}\left(\operatorname{constantPath}\left(\operatorname{inl}\left(\operatorname{nativeEndpoint}\left(p, \operatorname{true}\left(\right)\right)\right)\right)\right)\right)\land \operatorname{restrict}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right), \operatorname{immortal}\left(\right)\right)=\operatorname{map}\left(\operatorname{restrict}\left(\operatorname{originalTrajectory}\left(F\right), \operatorname{event}\left(omega, \operatorname{at}\left(omega, 0\right)=\operatorname{nativeEndpoint}\left(p, \operatorname{true}\left(\right)\right)\right)\right), \operatorname{includePath}\left(\right)\right)\land \operatorname{restrict}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right), \operatorname{immortal}\left(\right)\right)\le\operatorname{map}\left(\operatorname{originalTrajectory}\left(F\right), \operatorname{includePath}\left(\right)\right)\land \operatorname{AbsolutelyContinuous}\left(\operatorname{restrict}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right), \operatorname{immortal}\left(\right)\right), \operatorname{map}\left(\operatorname{originalTrajectory}\left(F\right), \operatorname{includePath}\left(\right)\right)\right)\land \operatorname{AE}\left(\operatorname{restrict}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right), \operatorname{immortal}\left(\right)\right), omega, \operatorname{pathDefect}\left(omega\right)=0\right)\land (\forall R: Real, 0\le R\Rightarrow\operatorname{restrict}\left(\operatorname{restrict}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right), \operatorname{immortal}\left(\right)\right), \operatorname{event}\left(omega, \operatorname{pathDefect}\left(omega\right)\le\operatorname{ofReal}\left(R\right)\right)\right)\le\operatorname{smul}\left(\frac{25}{6} \cdot \operatorname{ofReal}\left(\operatorname{exp}\left(\frac{25 \cdot R}{9}\right)\right), \operatorname{map}\left(\operatorname{originalTrajectory}\left(F\right), \operatorname{includePath}\left(\right)\right)\right))\land (\forall n: Nat, \operatorname{withDensity}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right), \operatorname{densityAt}\left(F, n\right)\right)=\operatorname{restrict}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right), \operatorname{immortal}\left(\right)\right)\land \operatorname{withDensity}\left(\operatorname{prefix}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right), n\right), \operatorname{terminalDensity}\left(F, n\right)\right)=\operatorname{prefix}\left(\operatorname{restrict}\left(\operatorname{killedTrajectory}\left(F, \operatorname{doob}\left(F, G\right), hsub\right), \operatorname{immortal}\left(\right)\right), n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.common_flow_immortal_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

originalTrajectory is the full homogeneous law of the actual C kernel with initial law nuP. includePath includes every original coordinate into the cemetery sum. The immortal restriction equals that original law restricted to the upper native initial descriptor and then included into the cemetery path space. More precisely it is the upper native atom mass times the Dirac law of the constant upper native path. On a positive native atom the original residual and successor results force C and M to be its actual Dirac row. The finite prefix masses and continuity from above identify the complete constant path. Its mass equals the total immortal mass, which proves equality on the full path sigma-algebra.

pathDefect is the sum over all times of the nonnegative real excess converted to ENNReal, with zero at the cemetery. The original excess is nonnegative on the original conull core. This series is zero almost everywhere under the immortal restriction. The whole immortal measure is dominated by the included original C law and is absolutely continuous with respect to it. In particular its restriction to pathDefect<=R, for every R>=0, satisfies the original local comparison constant (25/6)*exp(25R/9), obtained from h<=1/2, h>=3/25 and c=9/25.

Define terminalSurvival(F,inl(Q))=q(F,Q)/threeStepAverage(F,Q) and terminalSurvival(F,inr(unit))=0. densityAt(F,n) evaluates this function at time n on a full path; terminalDensity(F,n) evaluates it at the last coordinate of the prefix through n. prefix(mu,n) is the pushforward of mu under restriction to times zero through n. For every finite n, weighting the complete killed trajectory by densityAt(F,n) equals its immortal restriction. Consequently the immortal prefix is the killed prefix weighted by the terminal factor at X_n. The factor is preserved by the actual Doob action: harmonicity of q, cancellation of positive h, row absolute continuity and stationarity imply that its total expected mass is always the original native atom mass. The constant native path carries that whole mass, which proves the weighted identity on the full path sigma-algebra and then on each finite prefix.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.cemetery_markov`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.common_flow_doob_survival`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.common_flow_immortal_identity`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.common_flow_immortal_survival`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.homogeneous_initial`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.map_terminal_density`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass](MarkovPrefixMass.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelEndpointIdentification](NativeBorelEndpointIdentification.md)
