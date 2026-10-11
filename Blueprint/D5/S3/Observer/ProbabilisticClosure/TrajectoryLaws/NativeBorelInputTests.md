# Complete conditional rows

## Abstract

Full bounded Borel input tests

discrepancy(R,S,t,x) is the signed real difference R(x){t}-S(x){t}, using Measure.real after probability normalization establishes finiteness. InputTests(nu,R,S) means: for every complete target atom t and every Borel real input function phi with some finite pointwise absolute bound M, integral phi(x) discrepancy(R,S,t,x) dnu(x)=0. The bound may depend on phi and on the selected coordinate. JointInputTests(Gamma,H) uses the same quantifiers, with integral phi(z.first)*H(a,z) dGamma(z)=0. unnormalizedB(a,(Q,W)) means law(Q).real{prependB(a)}-(1-u(Q)).toReal*law(W).real{a}; unnormalizedA(a,(W,Q)) means law(W).real{prependA(a)}-v(W).toReal*law(Q).real{a}. This is signed real subtraction.

**Theorem 1.1 (normalizedB iff input tests).**

$$\forall nu: MeasurePDescriptor, \forall K: KernelPB, (\operatorname{IsProbabilityMeasure}\left(nu\right))\Rightarrow((\operatorname{IsMarkovKernel}\left(K\right))\Rightarrow((\operatorname{AE}\left(nu, Q, \operatorname{residualB}\left(Q\right)=\operatorname{barycenter}\left(\operatorname{beta}\left(\right), K, Q\right)\right))\Leftrightarrow(\operatorname{InputTests}\left(nu, \operatorname{residualB}\left(\right), \operatorname{barycenterFamily}\left(\operatorname{beta}\left(\right), K\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelInputTests.normalizedB_iff_input_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

KernelPB is a Markov kernel PDescriptor to BDescriptor, and barycenter(beta,K,Q) is lawKernel(beta) composed with K(Q). The statement assumes neither normalizedB nor a CommonFlow. Indicators of arbitrary measurable input sets give zero set integrals; integrability of each signed coordinate follows from the two probability bounds. The exact Mathlib set-integral uniqueness theorem proves one a.e. equality per atom. Only the countable complete atom family is intersected before singleton extensionality recovers full measure equality. Infinity is included; no uncountable intersection over input tests occurs.

**Theorem 1.2 (normalizedA iff input tests).**

$$\forall nu: MeasureBDescriptor, \forall K: KernelBP, (\operatorname{IsProbabilityMeasure}\left(nu\right))\Rightarrow((\operatorname{IsMarkovKernel}\left(K\right))\Rightarrow((\operatorname{AE}\left(nu, W, \operatorname{residualA}\left(W\right)=\operatorname{barycenter}\left(\operatorname{p}\left(\right), K, W\right)\right))\Leftrightarrow(\operatorname{InputTests}\left(nu, \operatorname{residualA}\left(\right), \operatorname{barycenterFamily}\left(\operatorname{p}\left(\right), K\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelInputTests.normalizedA_iff_input_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

KernelBP is a Markov kernel BDescriptor to PDescriptor. The same characterization is proved for residualA and barycenter(p,K,W), with the entire original input descriptor and its unweighted marginal. The displayed tests here are marginal integrals against the barycenter discrepancy. The full joint-test theorems below identify these marginal tests with signed tests on the same given joint law.

**Theorem 1.3 (input test joint identity).**

$$\forall s: ActivePhase, \forall t: ActivePhase, \forall nu: MeasureRegularDescriptor, \forall K: KernelRegularDescriptors, \forall Gamma: JointMeasure, \forall R: OppositeLawFamily, \forall a: ValidTail, \forall phi: BorelRealInputFunction, (\operatorname{JointIdentityHypotheses}\left(s, t, nu, K, Gamma, R, phi\right))\Rightarrow(\operatorname{MarginalSignedIntegral}\left(nu, K, R, a, phi\right)=\operatorname{JointSignedIntegral}\left(Gamma, R, a, phi\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelInputTests.input_test_joint_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

JointIdentityHypotheses means nu is a probability measure, K is Markov, Gamma=nu compProd K, R is measurable with every row a probability law, and phi is measurable with a finite absolute bound. MarginalSignedIntegral is integral phi(x)*[R(x).real{a}-barycenter(t,K,x).real{a}] dnu(x); JointSignedIntegral is integral phi(z.first)*[R(z.first).real{a}-law(z.second).real{a}] dGamma(z). For arbitrary phases s,t, a probability marginal nu, one Markov kernel K, and Gamma=nu compProd K, let R be any measurable family of full opposite probability laws. For every complete atom a and every bounded actual TV-Borel real input test phi, the integral of phi times [R{a}-barycenter{a}] over nu equals the integral of phi(z.first) times [R(z.first){a}-law(z.second){a}] over this same Gamma. Fubini is applied only after the joint signed integrand is shown bounded and integrable. Gamma is fixed before the test quantifiers.

**Theorem 1.4 (normalizedB iff full joint tests).**

$$\forall nu: MeasurePDescriptor, \forall K: KernelPB, \forall Gamma: JointMeasurePB, (\operatorname{IsProbabilityMeasure}\left(nu\right))\Rightarrow((\operatorname{IsMarkovKernel}\left(K\right))\Rightarrow((Gamma=\operatorname{compProd}\left(nu, K\right))\Rightarrow((\operatorname{AE}\left(nu, Q, \operatorname{residualB}\left(Q\right)=\operatorname{barycenter}\left(\operatorname{beta}\left(\right), K, Q\right)\right))\Leftrightarrow(\operatorname{JointInputTests}\left(Gamma, \operatorname{unnormalizedB}\left(\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelInputTests.normalizedB_iff_full_joint_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With nu a probability measure, B a Markov kernel and this fixed Gamma=nu compProd B, the full residualB equation almost everywhere is equivalent to zero integral against every bounded actual TV-Borel real input test and every complete beta atom of law(Q){prependB(a)}-(1-u(Q))*law(W){a}. The formula uses real masses after finiteness. Original denominator 1-u lies in [3/5,2/3]; multiplying and dividing the test by it preserve measurable boundedness. No normalized field is assumed.

**Theorem 1.5 (normalizedA iff full joint tests).**

$$\forall nu: MeasureBDescriptor, \forall K: KernelBP, \forall Gamma: JointMeasureBP, (\operatorname{IsProbabilityMeasure}\left(nu\right))\Rightarrow((\operatorname{IsMarkovKernel}\left(K\right))\Rightarrow((Gamma=\operatorname{compProd}\left(nu, K\right))\Rightarrow((\operatorname{AE}\left(nu, W, \operatorname{residualA}\left(W\right)=\operatorname{barycenter}\left(\operatorname{p}\left(\right), K, W\right)\right))\Leftrightarrow(\operatorname{JointInputTests}\left(Gamma, \operatorname{unnormalizedA}\left(\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelInputTests.normalizedA_iff_full_joint_tests` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete-coordinate topology theorem identifies actual TV-Borel with inherited Giry on each unchanged regular descriptor. For the reversed fixed joint Gamma=nu compProd A, the same equivalence uses law(W){prependA(a)}-v(W)*law(Q){a}, for every complete p atom. The original denominator v lies in [1/3,2/5], and its reciprocal is bounded by three. These are the same acquired joint realizations and their unweighted input margins, including the infinity test.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelInputTests.input_test_joint_identity`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelInputTests.normalizedA_iff_full_joint_tests`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelInputTests.normalizedA_iff_input_tests`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelInputTests.normalizedB_iff_full_joint_tests`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelInputTests.normalizedB_iff_input_tests`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology](NativeBorelTVTopology.md)
