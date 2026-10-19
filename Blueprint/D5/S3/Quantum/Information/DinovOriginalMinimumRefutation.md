# The within-DOF minimum clause of equipartition duality fails

## Abstract

At two degrees of freedom, a nonuniform phase density has the same joint action marginal as its uniform-phase product comparator and strictly smaller uncertainty in both degrees of freedom.

Real.Angle is the quotient AddCircle(2*pi), with angular volume of mass 2*pi. The action reference measure action is Lebesgue measure restricted to strictly positive reals. TorusOne is Real.Angle times the reals, TorusTwo is its square, and CartesianTwo is the square of a real coordinate pair. torusBase is angular volume times action; torusFullBase is its square. Cartesian volume is the standard product Lebesgue measure. The first Bool index selects the degree of freedom; the second selects q for false and p for true. Pair, fst and snd below denote ordered pairing and projections. integral, integralNN, ae, and withDensity use their indicated measures; ofReal is the nonnegative extended-real embedding. Function spaces and products are ordinary function and Cartesian product types.

## A fourth-harmonic application to state-level saturation uniqueness

This application concerns Conjecture 3.22(iii) of Ivo D. Dinov, arXiv:2607.07851v1, with the bound of Problem 3.17(b) and the Williamson convention of Theorem 3.13. The fourth-harmonic counterexample is attributed to prior mathematical work of Wenlin Zhang, Haobo Ma and Ivo D. Dinov; no first-discovery or matrix-inequality priority is asserted. The definitions used here are the existing DinovOriginalMinimumRefutation definitions displayed below: PsiA, PsiA2, sourcePullback, sourceTorusLaw, cartesianLaw, sourceState, commonActionMarginal, phaseUniformProduct, actualCovariance and sourceUncertainty.

The declared theorem result below remains solely the second-harmonic refutation of the minimum clause (ii). Its concluding sentence about assertions receiving no separate settlement refers to that theorem. The fourth-harmonic argument in this section has an archived, compiled exact specialization with standard-axiom evidence, but that specialization is unadmitted and is not a delivered library declaration. This exposition adds no Lean theorem; checking the existing owner's declarations does not newly compile or certify this application.

Fix n=2, the entropy lower threshold s=0, and r0(J1,J2)=exp(-(J1+J2)) on (0,infinity)^2. Angles lie in Real.Angle=AddCircle(2*pi). Their reference is angular Lebesgue volume of mass 2*pi, not probability-normalized Haar measure. Actions use action=volume restricted to J>0; torusBase is their angle-action product and torusFullBase its square. PsiA(theta,J)=(sqrt(2*J)*sin(theta),sqrt(2*J)*cos(theta)), in q,p order, and PsiA2 acts on both pairs. Lemma 2.3 supplies a smooth chart off zero action. Definition 2.4 and the static conjecture require probability densities on positive actions, without imposing smooth extension across the Cartesian zero-action planes. The witnesses below have the additional Borel, finite-entropy, L2 and positive-definiteness certificates in sourceState; these do not identify that subclass with the full source class.

The reference-volume transport can be seen directly through ordinary polar coordinates (r,t). Set H(r,t)=(t,r^2/2) for r>0 and -pi<t<pi. Its derivative matrix is [[0,1],[r,0]], its determinant is -r, and its inverse on the image is (t,J) mapped to (sqrt(2*J),t). Thus the Jacobian-weighted polar measure r dr dt maps under H to dt dJ. The real action-angle map composed with H is the polar map followed by the swap of the two Cartesian coordinates. The two Jacobian formulas and invariance of product Lebesgue measure under that swap give real-chart volume transport. The omitted ray and origin are null; replacing (-pi,pi) by (-pi,pi] changes no measure. AddCircle.measurePreserving_mk at period 2*pi and initial point -pi then passes to quotient angles. Consequently map(PsiA,torusBase)=volume and map(PsiA2,torusFullBase)=volume. This also explains why no angular entropy shift is introduced.

Let a4(theta)=(1+cos(4*theta)/2)/(2*pi) and a0(theta)=1/(2*pi), both as quotient-angle functions. They are continuous, strictly positive, normalized against angular volume, and bounded above by 1; specifically 1/(4*pi)<=a4<=3/(4*pi)<1. For a Cartesian pair write R=q^2+p^2 and P=p^4-6*p^2*q^2+q^4. Define f4(q,p)=exp(-R/2)*(1+P/(2*R^2))/(2*pi) when R>0, and f4(0,0)=0. Define g(q,p)=exp(-R/2)/(2*pi) also at the origin. For x=((q1,p1),(q2,p2)), put F4(x)=f4(q1,p1)*f4(q2,p2) and G(x)=g(q1,p1)*g(q2,p2). Here F4 and G name actual Cartesian density functions, not just angular profiles. The polynomial inequalities -R^2<=P<=R^2 give nonnegativity; the piecewise rational formula is Borel measurable and continuous where both radii are positive. The finite zero extension on the null zero-action planes is not a claim of continuity or smoothness there.

For J>0, R(PsiA(theta,J))=2*J and P(PsiA(theta,J))/R(PsiA(theta,J))^2=cos(4*theta). The latter follows from cos(4*theta)=8*cos(theta)^4-8*cos(theta)^2+1. Therefore f4(PsiA(theta,J))=a4(theta)*exp(-J), while g(PsiA(theta,J))=a0(theta)*exp(-J). For either a=a4 or a=a0, set h_a(theta,J)=a(theta)*exp(-J) and rho_a(z)=h_a(z1)*h_a(z2). The corresponding sourcePullback equals rho_a almost everywhere for torusFullBase. Since the angular integral of a and the positive-action integral of exp(-J) are both 1, rho_a has total mass 1. Weighted reference-volume transport gives map(PsiA2,sourceTorusLaw(F))=cartesianLaw(F), for F=F4 and F=G separately, and proves that all four source and Cartesian laws are probability measures.

The common action law is the full joint probability measure actionLaw(r0), whose density factors into the two normalized densities exp(-J1) and exp(-J2). For every positive action pair J, each angular fiber rho_a((theta1,J1),(theta2,J2)) is integrable on the compact angular square and its integral is exp(-(J1+J2))=r0(J). Thus both required almost-everywhere fiber certificates hold. Moreover map(actionProjection,sourceTorusLaw(F4))=actionLaw(r0), map(actionProjection,sourceTorusLaw(G))=actionLaw(r0), map(radialAction,cartesianLaw(F4))=actionLaw(r0), and map(radialAction,cartesianLaw(G))=actionLaw(r0). The last two equalities use radialAction composed with PsiA2 equal to actionProjection almost everywhere on positive actions, together with the weighted transports. These are all six components of commonActionMarginal, not a comparison of action means. G also satisfies phaseUniformProduct: its source density is r0(actionProjection(z))/(2*pi)^2 and its two action factors are individually normalized.

Entropy requires genuine integrability before transport. For either profile a, compactness and strict positivity make a and a*log(a) integrable on Real.Angle. The Gamma integrals at parameters 1 and 2 give integrability of exp(-J) and J*exp(-J) on positive actions. The identity h_a*log(h_a)=(a*log(a))*exp(-J)-a*(J*exp(-J)), with the two variables separated, proves one-pair log-density integrability. For the two-pair product, rho_a*log(rho_a) is the sum of (h_a*log(h_a)) in the first pair times h_a in the second and the reversed product, so it too is integrable. Measurability and reference-volume transport then prove integrability of F*log(F) on Cartesian volume and of sourcePullback(F)*log(sourcePullback(F)) on torusFullBase, and equality of these two integrals for each F separately. At zero density use the usual 0*log(0)=0 integral convention. On positive actions 0<rho_a<=1, hence -rho_a*log(rho_a)>=0. Accordingly sourceEntropy(F4)>=0 and sourceEntropy(G)>=0, so both meet s=0. No equality between these two state entropies is assumed or asserted.

For each of the angular laws a4(theta)dtheta and a0(theta)dtheta, the exact moments are E[sin(theta)]=E[cos(theta)]=E[sin(theta)*cos(theta)]=0 and E[sin(theta)^2]=E[cos(theta)^2]=1/2. One way to check every entry is to rewrite a4 as (3/2-4*cos(theta)^2+4*cos(theta)^4)/(2*pi), integrate cosine powers through degree six on [-pi,pi], and use the sine-times-cosine-power integral with equal endpoint cosines; sin(theta)^2=1-cos(theta)^2 supplies the remaining square. The uniform moments follow from the corresponding sine and cosine integrals. These are the first and second harmonic cancellations needed for covariance, with the fourth harmonic retained in the density.

Under either one-pair law, angle and action are independent and E[J]=integral(J*exp(-J),J>0)=1. Measurable coordinate squares are integrable: their weighted integrals separate into 2*integral(J*exp(-J)) times the bounded angular square integral. The actual coordinates therefore belong to L2 under the one-pair law, and product projection followed by PsiA2 transport gives MemLp 2 for all four actualCoordinate functions under each Cartesian law. This justifies the first and mixed moments, rather than presupposing finite covariance. Both Cartesian means vanish, E[q^2]=E[p^2]=1 and E[q*p]=0 within each pair. Independence of the two pairs and their zero means gives all cross-pair covariances zero. In q1,p1,q2,p2 order, all four diagonal entries are 1 and all twelve off-diagonal entries are 0: actualCovariance(cartesianLaw(F4))=I4=actualCovariance(cartesianLaw(G)). These are covariances of the realized probability laws. Matrix.PosDef.one establishes their positive definiteness, completing every sourceState component together with the normalization, entropy and transport facts above.

Use the source symplectic convention in the same order: Omega=diag([[0,1],[-1,0]],[[0,1],[-1,0]]). A frequency-one Williamson certificate requires 1>0 and a matrix S with S*Omega*S^T=Omega and S*Sigma*S^T=I4. For each actual covariance Sigma=I4, choose S=I4. Thus both positive frequencies are 1, with both matrix identities satisfied in the stated convention. Each actual q,p covariance block is I2, so sourceUncertainty(F4,j)=sqrt(det(I2))=1=sourceUncertainty(G,j) for every j in Bool. Both states simultaneously attain the per-DOF value 1 associated with their minimum symplectic frequency. This identity certificate does not prove a general Williamson theorem, general-spectrum bound or orbit-sharpness result.

The actual Cartesian probability laws are unequal. If cartesianLaw(F4)=cartesianLaw(G), uniqueness of withDensity densities over sigma-finite Lebesgue measure would give equality of their nonnegative real densities almost everywhere. On the open set where both radii are positive, both densities are continuous and Lebesgue measure has full support. Measure.eqOn_open_of_ae_eq would therefore force pointwise equality throughout that open set. At x=((0,1),(0,1)), each fourth-harmonic factor is 3/2 times the corresponding Gaussian factor, so F4(x)=(9/4)*G(x), with G(x)>0, a contradiction. The open-set argument is essential: a discrepancy at one point alone would not distinguish probability laws.

Specialize the source's state-level uniqueness assertion to n=2, s=0 and r0. Its necessary consequence says that a pair of sourceState densities with commonActionMarginal, a phaseUniformProduct comparator, both entropy lower bounds, both actual covariances I4, both positive frequency-one certificates and both all-j saturations must have equal Cartesian laws. Indeed uniqueness would identify the source states modulo null sets, hence their source laws; their PsiA2 pushforwards would then identify the Cartesian laws. F4 and G satisfy every antecedent just established and violate that consequence. This supplies the fourth-harmonic failure of the clause-(iii) specialization within the stated static source class. It neither invokes the earlier clause-(ii) contradiction nor replaces law inequality with angular pointwise nonuniformity. It leaves the fixed-covariance symplectic inequality intact: the two different density laws have exactly the same covariance and frequencies.

The reused suppliers are pinned Mathlib at db584cd6d46c92f209a44c0f1c829460d327499d with Lean v4.33.0. The transport uses map_withDensity_abs_det_fderiv_eq_addHaar, the polarCoord derivative and null-complement facts, AddCircle.measurePreserving_mk and Measure.map_prod_map. Integral transport and product decomposition use integral_map, MeasurePreserving.integrable_comp, integral_prod_mul and prod_withDensity; normalization and log-integrability use GammaIntegral_convergent and integral_exp_neg_Ioi_zero. The angular calculations use AddCircle.intervalIntegral_preimage, integral_cos_pow and integral_sin_pow_odd_mul_cos_pow. Actual L2 and covariance use memLp_two_iff_integrable_sq, memLp_map_measure_iff, covariance_map and covariance_fst_snd_prod; weighted-density uniqueness and Measure.eqOn_open_of_ae_eq give the law distinction. These applications are distinct from the frozen owner's clause-(ii) result, whose local proof steps are not exported helper declarations.

The wider Dinov program remains open here: general weighted-harmonic covariance and moment bridges, strict modulus and trace-energy equality; continuous conditional Gibbs/KL identities, normalized fibers and zero-KL equality; the actual Bessel normalization, derivatives, monotonicity, endpoints and inverse range; sharp centered iid variational minima, attainment and all equality cases, including common action-independent orientation, floor endpoints and the empty class above maximal entropy; derivative and endpoint regularity, smooth minimizers, exact harmonic entropy, Gaussian comparison and analytic noncentered improvement; non-iid joint-law KL and mutual-information decomposition and the exact attainable-area region with boundary equality cases; general canonical-pair symplectic bounds and orbit sharpness; and positive-diffusion stationary uniqueness, convergence and entropy production under the required solution regularity. No conclusion about pure transport dynamics, general n, a general symplectic spectrum or the whole conjecture's other assertions follows from this exposition.

**Definition 1.1 (The action-angle source map).**

$$\forall z \in TorusOne,\; \operatorname{PsiA}\left(z\right) = \operatorname{pair}\left(\operatorname{sqrt}\left(2 \cdot \operatorname{snd}\left(z\right)\right) \cdot \operatorname{sin}\left(\operatorname{fst}\left(z\right)\right), \operatorname{sqrt}\left(2 \cdot \operatorname{snd}\left(z\right)\right) \cdot \operatorname{cos}\left(\operatorname{fst}\left(z\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.PsiA` (`✓ std3`).

*Citation.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

The sine and cosine are those of the quotient angle. PsiA2 applies PsiA independently to the two coordinate pairs. R2(q,p)=q^2+p^2; radialAction takes R2/2 in each degree of freedom, and actionProjection takes the two action coordinates.

**Definition 1.2 (Covariance of the actual Cartesian coordinates).**

$$\forall mu \in \operatorname{Measure}\left(CartesianTwo\right),\; \forall i \in \operatorname{Product}\left(Bool, Bool\right),\; \forall k \in \operatorname{Product}\left(Bool, Bool\right),\; \operatorname{actualCovariance}\left(mu\right)\left(i, k\right) = \operatorname{covariance}\left(\operatorname{actualCoordinate}\left(i\right), \operatorname{actualCoordinate}\left(k\right), mu\right)$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.actualCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

Covariance is the integral of the centered product under the actual law. No covariance matrix is prescribed as a hypothesis.

**Definition 1.3 (Within-DOF uncertainty).**

$$\forall mu \in \operatorname{Measure}\left(CartesianTwo\right),\; \forall j \in Bool,\; \operatorname{actualUncertainty}\left(mu, j\right) = \operatorname{sqrt}\left(\operatorname{det}\left(\operatorname{covarianceBlock}\left(mu, j\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.actualUncertainty` (`✓ std3`).

*Citation.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

covarianceBlock(mu,j) is the two by two q,p principal block of actualCovariance(mu), in that order. The uncertainty is its determinant's nonnegative square root, as in Theorem 3.16.

**Definition 1.4 (The normalized Cartesian density law).**

$$\forall F \in CartesianTwo \to \mathbb{R},\; \operatorname{cartesianLaw}\left(F\right) = \operatorname{withDensity}\left(volume, \operatorname{fun} x \mapsto {\operatorname{ofReal}\left(F\left(x\right)\right)}\right)$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.cartesianLaw` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

Normalization and nonnegativity are requirements of sourceState; the density law itself is defined for every real-valued function.

**Definition 1.5 (Density pulled back through the source map).**

$$\forall F \in CartesianTwo \to \mathbb{R},\; \forall z \in TorusTwo,\; \operatorname{sourcePullback}\left(F, z\right) = F\left(\operatorname{PsiA2}\left(z\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.sourcePullback` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

sourceTorusLaw(F) is torusFullBase.withDensity(ofReal(sourcePullback(F))). It uses the actual quotient-angle source map.

**Definition 1.6 (Cartesian differential entropy).**

$$\forall F \in CartesianTwo \to \mathbb{R},\; \operatorname{sourceEntropy}\left(F\right) = -\operatorname{integral}\left(volume, \operatorname{fun} x \mapsto {F\left(x\right) \cdot \operatorname{log}\left(F\left(x\right)\right)}\right)$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.sourceEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

Entropy uses the natural logarithm. sourceUncertainty(F,j) is actualUncertainty(cartesianLaw(F),j). The finite integrals and the torus-to-Cartesian entropy identity are certified in sourceState.

**Definition 1.7 (A joint action density).**

$$\forall r \in \operatorname{Product}\left(\mathbb{R}, \mathbb{R}\right) \to \mathbb{R},\; \operatorname{actionDensity}\left(r\right) \Leftrightarrow {{\operatorname{Measurable}\left(r\right)} \land {{\forall J \in \operatorname{Product}\left(\mathbb{R}, \mathbb{R}\right),\; 0 \le r\left(J\right)} \land {\operatorname{integralNN}\left(\operatorname{prod}\left(action, action\right), \operatorname{fun} J \mapsto {\operatorname{ofReal}\left(r\left(J\right)\right)}\right) = 1}}}$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.actionDensity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

actionLaw(r) is the action product measure weighted by ofReal(r). oneActionDensity is the same measurable, nonnegative, unit-mass condition for one action coordinate.

**Definition 1.8 (Finite-entropy states with their source realization).**

$$\forall F \in CartesianTwo \to \mathbb{R},\; \operatorname{sourceState}\left(F\right) \Leftrightarrow {{\operatorname{Measurable}\left(F\right)} \land {{\forall x \in CartesianTwo,\; 0 \le F\left(x\right)} \land {{\operatorname{IsProbabilityMeasure}\left(\operatorname{cartesianLaw}\left(F\right)\right)} \land {{\operatorname{Integrable}\left(\operatorname{fun} x \mapsto {F\left(x\right) \cdot \operatorname{log}\left(F\left(x\right)\right)}, volume\right)} \land {{\forall i \in \operatorname{Product}\left(Bool, Bool\right),\; \operatorname{MemLp}\left(\operatorname{actualCoordinate}\left(i\right), 2, \operatorname{cartesianLaw}\left(F\right)\right)} \land {{\operatorname{PosDef}\left(\operatorname{actualCovariance}\left(\operatorname{cartesianLaw}\left(F\right)\right)\right)} \land {{\operatorname{Integrable}\left(\operatorname{fun} x \mapsto {\operatorname{sourcePullback}\left(F, x\right) \cdot \operatorname{log}\left(\operatorname{sourcePullback}\left(F, x\right)\right)}, torusFullBase\right)} \land {{\operatorname{integral}\left(torusFullBase, \operatorname{fun} x \mapsto {\operatorname{sourcePullback}\left(F, x\right) \cdot \operatorname{log}\left(\operatorname{sourcePullback}\left(F, x\right)\right)}\right) = \operatorname{integral}\left(volume, \operatorname{fun} x \mapsto {F\left(x\right) \cdot \operatorname{log}\left(F\left(x\right)\right)}\right)} \land {\operatorname{map}\left(PsiA2, \operatorname{sourceTorusLaw}\left(F\right)\right) = \operatorname{cartesianLaw}\left(F\right)}}}}}}}}}$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.sourceState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

The density is Borel measurable, pointwise nonnegative and normalized on Cartesian volume. Every one of its four Cartesian coordinates belongs to L2, and its full four by four actual covariance is positive definite. Both entropy integrands are integrable; their integrals agree, and PsiA2 pushes the actual source law to the Cartesian density law. These extra certificates restrict the universal comparison and are all established for the counterexample.

**Definition 1.9 (The same joint marginal in both representations).**

$$\forall F \in CartesianTwo \to \mathbb{R},\; \forall G \in CartesianTwo \to \mathbb{R},\; \forall r \in \operatorname{Product}\left(\mathbb{R}, \mathbb{R}\right) \to \mathbb{R},\; \operatorname{commonActionMarginal}\left(F, G, r\right) \Leftrightarrow {{\operatorname{ae}\left(\operatorname{prod}\left(action, action\right), \operatorname{fun} J \mapsto {{\operatorname{Integrable}\left(\operatorname{fun} ts \mapsto {\operatorname{sourcePullback}\left(F, \operatorname{pair}\left(\operatorname{pair}\left(\operatorname{fst}\left(ts\right), \operatorname{fst}\left(J\right)\right), \operatorname{pair}\left(\operatorname{snd}\left(ts\right), \operatorname{snd}\left(J\right)\right)\right)\right)}, volume\right)} \land {\operatorname{integral}\left(volume, \operatorname{fun} ts \mapsto {\operatorname{sourcePullback}\left(F, \operatorname{pair}\left(\operatorname{pair}\left(\operatorname{fst}\left(ts\right), \operatorname{fst}\left(J\right)\right), \operatorname{pair}\left(\operatorname{snd}\left(ts\right), \operatorname{snd}\left(J\right)\right)\right)\right)}\right) = r\left(J\right)}}\right)} \land {{\operatorname{ae}\left(\operatorname{prod}\left(action, action\right), \operatorname{fun} J \mapsto {{\operatorname{Integrable}\left(\operatorname{fun} ts \mapsto {\operatorname{sourcePullback}\left(G, \operatorname{pair}\left(\operatorname{pair}\left(\operatorname{fst}\left(ts\right), \operatorname{fst}\left(J\right)\right), \operatorname{pair}\left(\operatorname{snd}\left(ts\right), \operatorname{snd}\left(J\right)\right)\right)\right)}, volume\right)} \land {\operatorname{integral}\left(volume, \operatorname{fun} ts \mapsto {\operatorname{sourcePullback}\left(G, \operatorname{pair}\left(\operatorname{pair}\left(\operatorname{fst}\left(ts\right), \operatorname{fst}\left(J\right)\right), \operatorname{pair}\left(\operatorname{snd}\left(ts\right), \operatorname{snd}\left(J\right)\right)\right)\right)}\right) = r\left(J\right)}}\right)} \land {{\operatorname{map}\left(actionProjection, \operatorname{sourceTorusLaw}\left(F\right)\right) = \operatorname{actionLaw}\left(r\right)} \land {{\operatorname{map}\left(actionProjection, \operatorname{sourceTorusLaw}\left(G\right)\right) = \operatorname{actionLaw}\left(r\right)} \land {{\operatorname{map}\left(radialAction, \operatorname{cartesianLaw}\left(F\right)\right) = \operatorname{actionLaw}\left(r\right)} \land {\operatorname{map}\left(radialAction, \operatorname{cartesianLaw}\left(G\right)\right) = \operatorname{actionLaw}\left(r\right)}}}}}}$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.commonActionMarginal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

For almost every positive action pair J, both angular fibers are integrable and their integrals equal r(J). Both source-law action projections and both Cartesian radial-action projections equal actionLaw(r). Marginal equality is joint equality for the same two actions.

**Definition 1.10 (The phase-uniform product comparator).**

$$\forall G \in CartesianTwo \to \mathbb{R},\; \forall r \in \operatorname{Product}\left(\mathbb{R}, \mathbb{R}\right) \to \mathbb{R},\; \operatorname{phaseUniformProduct}\left(G, r\right) \Leftrightarrow {{\operatorname{aeEq}\left(torusFullBase, \operatorname{sourcePullback}\left(G\right), \operatorname{fun} z \mapsto {\frac{r\left(\operatorname{actionProjection}\left(z\right)\right)}{{2 \cdot \pi}^{2}}}\right)} \land {\exists rone \in \mathbb{R} \to \mathbb{R},\; \exists rtwo \in \mathbb{R} \to \mathbb{R},\; {\operatorname{oneActionDensity}\left(rone\right)} \land {{\operatorname{oneActionDensity}\left(rtwo\right)} \land {\operatorname{aeEq}\left(\operatorname{prod}\left(action, action\right), r, \operatorname{fun} J \mapsto {rone\left(\operatorname{fst}\left(J\right)\right) \cdot rtwo\left(\operatorname{snd}\left(J\right)\right)}\right)}}}}$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.phaseUniformProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

The source density equals r(actionProjection(z))/(2*pi)^2 almost everywhere. The joint action density factors almost everywhere into two actually normalized nonnegative one-action densities. This condition certifies existence of the product comparator.

**Definition 1.11 (The necessary two-DOF minimum assertion).**

$$dinovTwoDofMinimumClause \Leftrightarrow {\forall s \in \mathbb{R},\; \forall r \in \operatorname{Product}\left(\mathbb{R}, \mathbb{R}\right) \to \mathbb{R},\; \forall F \in CartesianTwo \to \mathbb{R},\; \forall G \in CartesianTwo \to \mathbb{R},\; {\operatorname{actionDensity}\left(r\right)} \Rightarrow {{\operatorname{sourceState}\left(F\right)} \Rightarrow {{\operatorname{sourceState}\left(G\right)} \Rightarrow {{\operatorname{commonActionMarginal}\left(F, G, r\right)} \Rightarrow {{\operatorname{phaseUniformProduct}\left(G, r\right)} \Rightarrow {{s \le \operatorname{sourceEntropy}\left(F\right)} \Rightarrow {{s \le \operatorname{sourceEntropy}\left(G\right)} \Rightarrow {\forall j \in Bool,\; \operatorname{sourceUncertainty}\left(G, j\right) \le \operatorname{sourceUncertainty}\left(F, j\right)}}}}}}}}$$

*Formalization.* `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.dinovTwoDofMinimumClause` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

Conjecture 3.22 (Equipartition duality): "Fix n ≥ 2, an entropy value s, and an action marginal ρ_J on (0,∞)^n. Among all states on T^n × (0,∞)^n with entropy ≥ s and action marginal ρ_J, the phase-equipartitioned product state (unique when it exists) simultaneously (i) maximizes the entropy, (ii) minimizes every within-DOF uncertainty u_j, and (iii) is the unique state at which the per-DOF conjectured bound of Problem 3.17(b) is saturated for all j; moreover it is the unique fixed point, with the given marginal, of the multi-DOF kime-deformed semigroup ∂t ρ = Σj (−ωj ∂θj + ε ∂θj²) ρ." The formal predicate expresses only a necessary specialization of clause (ii), at n=2, on the certified finite-entropy, L2, positive-definite subclass. The original all-n assertion implies clause (ii), which implies this specialization. The predicate has no n quantifier and makes no separate assertion about clauses (i), (iii), or the semigroup.

**Theorem 1.12 (Both uncertainties are smaller than the comparator's).**

$$\neg dinovTwoDofMinimumClause$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/dinov-2026-equipartition-duality-minimum-refutation` (refuted) by `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dinov-2026-equipartition-duality-minimum-refutation","declaration_gid":"D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ivo D. Dinov (2026). *Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom*. DOI: [10.48550/arxiv.2607.07851](https://doi.org/10.48550/arxiv.2607.07851). URL: <https://arxiv.org/abs/2607.07851v1>.

*Commentary.*

Use r(J1,J2)=exp(-(J1+J2)) and independent phases phi(theta)=(1+cos(2*theta)/2)/(2*pi). Each action has density exp(-J), and the comparator has uniform phases. The two Cartesian densities are the products of the actual one-DOF densities exp(-R2/2)*(1+(p^2-q^2)/(2*R2))/(2*pi) and exp(-R2/2)/(2*pi); the first is set to zero at R2=0. The zero-action planes have zero measure. Change of variables proves normalization, the source pushforwards, common joint marginal and entropy equality. Both entropies are finite and nonnegative, so s=0 is admissible. The actual covariance matrices, ordered q1,p1,q2,p2, are diag(3/4,5/4,3/4,5/4) and the identity. Both are positive definite and all coordinates belong to L2. For each of the two degrees of freedom the uncertainties are sqrt(15/16) and 1, respectively, with sqrt(15/16)<1. Adding both strict comparisons contradicts the sum of both inequalities required by the minimum assertion. Thus clause (ii), and hence the simultaneous conjecture as written, fails. Entropy maximization, saturation uniqueness and semigroup claims receive no separate settlement here.

## References

- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.PsiA`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.actionDensity`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.actualCovariance`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.actualUncertainty`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.cartesianLaw`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.commonActionMarginal`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.dinovTwoDofMinimumClause`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.phaseUniformProduct`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.sourceEntropy`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.sourcePullback`
- Truth anchor: `D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.sourceState`
