# Finite installed laws and the continuous boundary

## Abstract

Excluding every original finite COMPLETE realization

## The continuous endpoint-box common flow

For x in the original half-open interval [239/1000,6/25), the construction uses q=1944/390625, g=q/x^3, u=1-g-x and v=x/(g+x). The complete p and beta laws include the infinity coordinate, satisfy the original normalization and tail equations, and remain in every original endpoint box with a=1/3, b=2/5, c=9/25 and z=6/25.

realMass(mu,t) denotes mu.real({t}), and singletonMass(mu,x) denotes mu({x}). mass(mu,univ) and mass(mu,tailSet(s,n)) are evaluations at those sets; mass(mu,infinity(s)) and mass(mu,nativeEndpoint(s,b)) are singleton evaluations. integrand(x,f(x)) binds x in the indicated integral or integrability expression. Powers of a CurveParameter use its real value.

Measurable strict splitting means that every measurable E of positive mass has a measurable D contained in E with 0 < mu(D) < mu(E). For each of the two margins and two joint graph measures, recover x from the ratio of consecutive marker-one coordinates of its first descriptor. Push the restriction to E forward through this same recovery map. This finite real measure is dominated by the original uniformReal measure and has null singletons. The integral of 1 over Iio(b) is a continuous primitive, zero at 239/1000 and equal to the entire restricted mass at 6/25. The intermediate value theorem gives a half-mass cut. Pulling this cut back supplies the required measurable subpiece, including for arbitrary measurable E, not only singletons.

On the actual curveUniform conull carrier x < 6/25 and x > 0. Since q=(9/25)(6/25)^3, g=q/x^3 is strictly greater than 9/25. The same strict positive excess holds almost everywhere on its original p descriptor marginal. Apply NativeBorelCEvent.common_flow_event_localization to this continuousCommonFlow: its actual eventProbability is startedC(continuousCommonFlow,Q)(summableExcess), and nonzero event probability would force excess(Q)=0. Hence this original summable-excess event has probability zero at almost every actual p descriptor. The acquired kernels still retain this same x; no event, measure or realization is replaced.

**Theorem 1.1 (The Borel recovery map).**

$$\forall s: ActivePhase, (\operatorname{Measurable}\left(\operatorname{recoveredParameter}\left(s\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.recovered_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recovery ratio is defined on the entire original regular descriptor carrier. The positive lower cutoff in its denominator makes it Borel in both phases.

**Theorem 1.2 (Recovery on the same curve).**

$$\forall s: ActivePhase, (\forall t: CurveParameter, (\operatorname{recoveredParameter}\left(s, \operatorname{curveDescriptor}\left(s, t\right)\right)=t))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.recovered_curve` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every curve parameter, both recovery maps return its real value. This same supplier is used in curve injectivity, the acquired same-parameter successor and measurable splitting.

### The original half-open real carrier

$$
\operatorname{AE}\left(uniformReal, x, \operatorname{member}\left(x, \operatorname{Ico}\left(\frac{239}{1000}, \frac{6}{25}\right)\right)\right)
$$

uniformReal is 1000 times Lebesgue measure restricted to Ico(239/1000,6/25). The displayed set has full measure.

### Exact real parameter pushforward

$$
\operatorname{map}\left(curveUniform, parameterValue\right)=uniformReal
$$

parameterValue is Subtype.val from CurveParameter to the real line. Its pushforward is exactly uniformReal, so the real integrals and parameter integrals use the same original law.

**Theorem 1.3 (The original averaged coordinate as a moment).**

$$\forall n: Nat, (\operatorname{averagedCompletion}\left(n\right)=\operatorname{integral}\left(curveUniform, \operatorname{integrand}\left(t, \operatorname{curveG}\left(t\right) \cdot \operatorname{pow}\left(t, n\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.averaged_parameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integrand binds t:CurveParameter and uses its real coercion. This exact moment representation is consumed by the averaged formulas, negative recurrence and the arbitrary finite-observer obstruction.

**Theorem 1.4 (Every original moment is integrable).**

$$\forall n: Nat, (\operatorname{Integrable}\left(\operatorname{integrand}\left(t, \operatorname{curveG}\left(t\right) \cdot \operatorname{pow}\left(t, n\right)\right), curveUniform\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.moment_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integrand binds t:CurveParameter. Every natural power is integrable against the original finite parameter law; this supplies the finite polynomial-moment expansions.

### Strict upper inequality on the actual parameter carrier

$$
\operatorname{AE}\left(curveUniform, t, t<\frac{6}{25}\right)
$$

The original half-open carrier excludes the upper endpoint almost everywhere. The conclusion is used by the strict negative recurrence and strict positive excess applications.

**Theorem 1.5 (Complete regular descriptors and residual coordinates).**

$$(\forall s: ActivePhase, (\operatorname{Measurable}\left(\operatorname{curveDescriptor}\left(s\right)\right)))\land (\forall t: CurveParameter, ((\forall n: Nat, (\forall i: Letter, (\operatorname{realMass}\left(\operatorname{law}\left(\operatorname{curveDescriptor}\left(p, t\right)\right), \operatorname{pAtom}\left(n, i\right)\right)=\operatorname{if}\left(i=0, \operatorname{curveU}\left(t\right), \operatorname{curveG}\left(t\right)\right) \cdot \operatorname{pow}\left(t, n\right))))\land ((\forall n: Nat, (\forall i: Letter, (\operatorname{realMass}\left(\operatorname{law}\left(\operatorname{curveDescriptor}\left(beta, t\right)\right), \operatorname{betaAtom}\left(n, i\right)\right)=\operatorname{curveV}\left(t\right) \cdot \operatorname{if}\left(i=0, \operatorname{curveU}\left(t\right), \operatorname{curveG}\left(t\right)\right) \cdot \operatorname{pow}\left(t, n\right))))\land ((\forall s: ActivePhase, ((\operatorname{mass}\left(\operatorname{law}\left(\operatorname{curveDescriptor}\left(s, t\right)\right), univ\right)=1)\land ((\operatorname{mass}\left(\operatorname{law}\left(\operatorname{curveDescriptor}\left(s, t\right)\right), \operatorname{infinity}\left(s\right)\right)=0)\land ((\operatorname{mass}\left(\operatorname{law}\left(\operatorname{curveDescriptor}\left(s, t\right)\right), \operatorname{tailSet}\left(s, 0\right)\right)=\operatorname{if}\left(s=p, 1, \operatorname{ofReal}\left(\operatorname{curveV}\left(t\right)\right)\right))\land (\operatorname{EndpointBox}\left(\operatorname{curveDescriptor}\left(s, t\right)\right))))))\land ((\operatorname{residualB}\left(\operatorname{curveDescriptor}\left(p, t\right)\right)=\operatorname{law}\left(\operatorname{curveDescriptor}\left(beta, t\right)\right))\land (\operatorname{residualA}\left(\operatorname{curveDescriptor}\left(beta, t\right)\right)=\operatorname{law}\left(\operatorname{curveDescriptor}\left(p, t\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.continuous_descriptor_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The curve is measurable in the descriptor space. Both acquired residuals are the exact opposite-phase laws on the same parameter, and all finite and infinite coordinates, tails and endpoint boxes are retained.

### A same-parameter CommonFlow with null singletons

$$
(\forall Q: PDescriptor, (\operatorname{singletonMass}\left(\operatorname{nuP}\left(continuousCommonFlow\right), Q\right)=0))\land ((\forall W: BDescriptor, (\operatorname{singletonMass}\left(\operatorname{nuB}\left(continuousCommonFlow\right), W\right)=0))\land ((\forall Z: PDescriptorTimesBDescriptor, (\operatorname{singletonMass}\left(\operatorname{GammaB}\left(continuousCommonFlow\right), Z\right)=0))\land ((\forall Z: BDescriptorTimesPDescriptor, (\operatorname{singletonMass}\left(\operatorname{GammaA}\left(continuousCommonFlow\right), Z\right)=0))\land ((\forall s: ActivePhase, (\forall b: Bool, (\operatorname{if}\left(s=p, \operatorname{mass}\left(\operatorname{nuP}\left(continuousCommonFlow\right), \operatorname{nativeEndpoint}\left(p, b\right)\right), \operatorname{mass}\left(\operatorname{nuB}\left(continuousCommonFlow\right), \operatorname{nativeEndpoint}\left(beta, b\right)\right)\right)=0)))\land (\forall x: CurveParameter, ((\operatorname{B}\left(continuousCommonFlow, \operatorname{curveDescriptor}\left(p, x\right)\right)=\operatorname{dirac}\left(\operatorname{curveDescriptor}\left(beta, x\right)\right))\land ((\operatorname{A}\left(continuousCommonFlow, \operatorname{curveDescriptor}\left(beta, x\right)\right)=\operatorname{dirac}\left(\operatorname{curveDescriptor}\left(p, x\right)\right))\land (\operatorname{C}\left(continuousCommonFlow, \operatorname{curveDescriptor}\left(p, x\right)\right)=\operatorname{dirac}\left(\operatorname{curveDescriptor}\left(p, x\right)\right)))))))))
$$

The uniform parameter law is pushed forward to both descriptor margins and to both graph measures. Singleton masses vanish for all four measures, including the explicitly quantified nativeEndpoint(s,b) singleton in each phase, while B and A are deterministic only along the same retained parameter x; their return composition is the identity on the curve.

### continuous average integral

$$
\forall n: Nat, (\operatorname{averagedCompletion}\left(n\right)=1000 \cdot \operatorname{integralIco}\left(\frac{239}{1000}, \frac{6}{25}, \operatorname{integrand}\left(x, \operatorname{curveG}\left(x\right) \cdot \operatorname{pow}\left(x, n\right)\right)\right))
$$

The average is 1000 times the Lebesgue integral of g(x)x^n over Ico(239/1000,6/25). This is the exact normalized uniform law on the original half-open interval.

### continuous average formula

$$
\forall k: Nat, (\frac{\operatorname{averagedCompletion}\left(k + 3\right)}{\operatorname{pow}\left(\frac{6}{25}, k + 3\right)}=\frac{\frac{432}{5} \cdot (1-\operatorname{pow}\left(\frac{239}{240}, k + 1\right))}{k + 1})
$$

For every tail index k the normalized average has the exact factor (432/5)(1-(239/240)^(k+1))/(k+1).

### continuous average coefficient

$$
\operatorname{Tendsto}\left(\operatorname{sequence}\left(k, \left(k + 1\right) \cdot \frac{\operatorname{averagedCompletion}\left(k + 3\right)}{\operatorname{pow}\left(\frac{6}{25}, k + 3\right)}\right), atTop, \operatorname{Nhds}\left(\frac{432}{5}\right)\right)
$$

The sequence (k+1) times the displayed normalized average converges to 432/5. All four actual measures admit measurable strict splitting, and the same continuous carrier has strict positive excess, as explained above. The obstruction to arbitrary finite COMPLETE realizations is developed from the complete continuous moments and the actual installed-law transfer equation in NativeBorelFiniteCompleteObstruction.

### continuous negative recurrence

$$
\forall n: Nat, (\operatorname{recurrenceResidual}\left(n\right)<0)
$$

Write m(n)=averagedCompletion(n). Here recurrenceResidual(n) denotes m(n+2)-(2/9+6/25)*m(n+1)+(2/9)*(6/25)*m(n). The exact moment representation and integrability identify it with the integral of curveG(x)*x^n*(x-2/9)*(x-6/25) against the same curveUniform law. On its conull half-open carrier, curveG(x)>0, x>2/9 and x<6/25, so this integrable expression has strictly negative integral for every natural n, including 0, 1 and 2. Failure of this fixed two-root recurrence alone does not exclude every finite carrier; the finite COMPLETE exclusion uses the all-order polynomial-moment argument and actual installed-law transfer in NativeBorelFiniteCompleteObstruction.

NativeFiniteWordCoordinates owns the periodic curve parameters and the installed cylinder-transfer suppliers. Their original declaration namespace is retained. The full continuous descriptors, common flow, moment obstruction and finite COMPLETE conclusion are owned here.

Z is any finite original COMPLETE carrier with its measurable space and measurable singletons. M is its original Observer with source-independent initialization and acquired-operation update rows. e is any lawful InstalledEmitter(M), with arbitrary real probability tables. rho is any starting configuration PMF on this same Z. sumConfigurations is sum over z of rho(z).toReal times the real singleton mass of the actual tailLaw(M,e,p,z). It therefore includes arbitrary original acquired starting distributions.

All moments are the original averagedCompletion(n), the integral of g(x)x^n against curveUniform on [239/1000,6/25). For a real polynomial p, recurrenceSum(p,N,n) is the sum over i in p.support of p.coeff(i) averagedCompletion(N+n+i). Every finite order and every finite initial offset N is included.

**Theorem 1.6 (No nonzero recurrence).**

$$\forall p: RealPolynomial, \forall N: Nat, \operatorname{nonzero}\left(p\right)\Rightarrow\exists n:Nat, \operatorname{nonzero}\left(\operatorname{recurrenceSum}\left(p, N, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.continuous_no_linear_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero p, its real roots form a finite set. The continuous parameter measure assigns that set zero mass, while g(x)x^N is strictly positive. Thus the integral of g(x)x^N p(x)^2 is strictly positive. Expanding one polynomial factor gives the finite weighted sum of polynomial moments. If every recurrenceSum vanished, expanding the other factor would make the same positive integral zero. The same continuous measure supplies every moment.

**Theorem 1.7 (No finite-dimensional homogeneous linear realization).**

$$\forall V: FiniteRealModule, \forall T: EndV, \forall x: V, \forall ell: RealLinearFunctionalV, \forall N: Nat, \operatorname{Not}\left(\forall n: Nat, \operatorname{averagedCompletion}\left(N + n\right)=\operatorname{apply}\left(ell, \operatorname{apply}\left(\operatorname{pow}\left(T, n\right), x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.continuous_no_finite_linear_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FiniteRealModule is any real module with AddCommGroup and Module.Finite. T is any linear endomorphism, x any vector and ell any real linear functional. LinearMap.exists_monic_and_aeval_eq_zero supplies a nonzero monic annihilator for T. Applying ell to its action on T^n x gives exactly a finite recurrence. The continuous-moment result excludes equality of the entire sequence, after every finite initial offset. This consumed helper supplies the obstruction for the original installed laws below.

**Theorem 1.8 (No finite COMPLETE observer realizes even the averaged marker-one sequence).**

$$\forall Z: FiniteCompleteCarrier, \forall M: ObserverZ, \forall e: InstalledEmitterM, \forall rho: PMFZ, \forall N: Nat, \operatorname{Not}\left(\forall n: Nat, \operatorname{averagedCompletion}\left(N + n\right)=\operatorname{sumConfigurations}\left(rho, \operatorname{tailLaw}\left(M, e, p\right), \operatorname{pAtom}\left(n, 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.continuous_no_finite_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the actual marked-law regeneration equation on Marked(Z)=Z times Option(Operation). Mask each transition by the letter read from its incoming mark, exactly as rawFrom does. The two masks for beta then alpha give a homogeneous real linear endomorphism on the finite vector space of functions on Marked(Z). The complete word pWord(n,1) is n repetitions of [1,0] followed by [1,1]. Its exact stopped-word fiber is the corresponding prefix cylinder, so its actual tail singleton mass is the n-th power of that endomorphism applied to the final [1,1] cylinder vector. The original rho gives a linear readout at (z,none). This earns the finite-dimensional realization equation from the installed laws themselves. The continuous moment obstruction then excludes it for every finite carrier, every lawful emission table, every acquired update table and every rho, already at one mandatory full-law coordinate. Every finite offset N is also excluded.

The strictly negative two-endpoint recurrence is one diagnostic of this same continuous law. Exclusion of arbitrary finite COMPLETE carriers uses the stronger obstruction to every finite-order recurrence and the actual installed-law transfer equation. The finite matrices here describe the existing complete carrier mathematically; no analysis coordinate is installed as a new observer register.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.averaged_parameter`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.continuous_descriptor_family`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.continuous_no_finite_complete`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.continuous_no_finite_linear_realization`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.continuous_no_linear_recurrence`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.moment_integrable`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.recovered_curve`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteCompleteObstruction.recovered_measurable`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelFiniteProducts](NativeBorelFiniteProducts.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFiniteWordCoordinates](NativeFiniteWordCoordinates.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw](NativeInstalledFullLaw.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePeriodicWordLaw](NativePeriodicWordLaw.md)
