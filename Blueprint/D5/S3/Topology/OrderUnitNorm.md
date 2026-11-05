# The original order-unit norm

## Abstract

The original Archimedean order-unit cone gives an exact norm and a quantitative preparation criterion for the same positive unital exponential group.

Let E be any finite-dimensional real normed vector space. Its auxiliary norm supplies the usual topology only. The data A consist of a convex cone C containing zero, a closedness proof, salience, and a specified vector u in its interior. Salience means that a vector and its negative can both belong to C only when the vector vanishes. No inner product, lattice, Jordan product, self-duality or nonzero-dimension assumption is used.

Put B equal to the vectors v for which u-v and u+v belong to C. For each v, let S(v) be the nonnegative real radii r for which r u-v and r u+v belong to C, and let n(v) be inf S(v). In particular, zero is retained among the radii. The order relation is exactly w-v in C.

**Theorem 1.1 (The norm axioms follow from the original cone).**

$$\forall E \in Types,\; RealNormedVectorSpace\left(E\right) \Rightarrow \left(\forall A \in ConeUnitData\left(E\right),\; \forall v \in E,\; 0 \le n\left(v\right) \land \left(\left(n\left(v\right) = 0 \Leftrightarrow v = 0\right) \land \left(\left(\forall a \in R,\; n\left(smul\left(a, v\right)\right) = abs\left(a\right) \cdot n\left(v\right)\right) \land \left(\forall w \in E,\; n\left(v + w\right) \le n\left(v\right) + n\left(w\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrderUnitNorm.norm_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The symbols R and Types denote the real scalars and the type universe. ConeUnitData denotes precisely the original cone and unit data stated above. The displayed norm laws apply to the copy of E with norm n; this first assertion does not require finite dimension. They are proved rather than supplied as an extra hypothesis. The interior-unit assumption makes B a neighborhood of zero and hence absorbent. Each S(v) is nonempty, closed and bounded below by zero, so its infimum is attained.

The symmetric interval is convex and balanced. Its gauge equals n exactly: every positive gauge radius is an order radius, and every radius just above the attained order radius is a positive gauge radius. This includes v=0, where S(0) contains its infimum zero although the gauge uses strictly positive radii. Mathlib's gaugeSeminorm supplies the seminorm laws. At n(v)=0 the attained inequalities put v and -v in C, so salience supplies definiteness.

## Positive functionals and the same original operator

These are applications of the constructed norm and existing operator theory. In Lean, Data.operatorBounds(H * H) is exactly the set of nonnegative c with n(H(H(v))) at most c n(v) for every v. ContinuousLinearMap.norm_def identifies its infimum with the norm of Data.operator(H * H); definitional conjugation identifies that operator with the square of Data.operator(H), and ContinuousLinearMap.isLeast_opNorm proves attainment and minimality. The transported positive functional is Data.functional(beta); its upper norm bound follows from Data.positive_bound and ContinuousLinearMap.opNorm_le_bound, and evaluation at the unit gives the reverse inequality via ContinuousLinearMap.le_opNorm_of_le. NormedSpace.map_exp applied to Data.bridge.conjContinuousAlgEquiv gives the exponential transport.

PositiveDual denotes all original real-linear functionals nonnegative on C, and Effects denotes all x with x and u-x in C. RealEndomorphisms denotes all original real-linear maps E to E. The notation K abbreviates the norm of the square of the transported operator, and IsLeast includes membership and minimality in operatorBounds(H squared), the nonnegative global order-norm bound set. Here j is the canonical linear wrapping map to the copy E_u, and H_u is defined solely by H_u(j(v))=j(H(v)). The constructed copy is complete. The wrapping map and its inverse are continuous in the original finite-dimensional topology; no equality with the auxiliary ambient norm is asserted.

For every positive original real-linear functional beta, its evaluation is bounded by its mass beta(u) times n(v). Applying beta to the attained endpoint inequalities proves this without dividing by its mass. Thus mass zero forces the original functional to vanish. The operator norm of beta transported to E_u is exactly beta(u), including in dimension zero.

The square H_u squared acts on j(v) as j(H(H(v))). Its operator norm is exactly the infimum of all nonnegative c satisfying n(H(H(v))) at most c n(v) for every original v. This infimum is attained. Neither an ambient operator bound nor the square of the norm of H is substituted for this number.

A positive unital linear map contracts n. A linear equivalence whose inverse is also positive is an isometry; positivity and unitality alone do not imply isometry. Applying this conclusion to exp(tH) uses both the assumed positivity at t and at -t. Independently, H(u)=0 makes the derivative of exp(tH)u vanish on the whole real line, so the actual exponential fixes u. Conjugation by j carries the actual exponential to exp(tH_u).

Assume that every original exp(tH) is positive and fixes u. Its order norm is then preserved for every real t. If the separately supplied condition H(u)=0 also holds, an effect x in C with u-x in C has centered vector z=x-u/2 of order norm at most one half, and H(H(x))=H(H(z)). Positive-functional domination and the exact square-operator bound give the all-time centered-orbit estimate.

The actual scalar orbit f(t)=beta(exp(tH)x) is twice continuously differentiable, with first derivative beta(exp(tH)Hx) and second derivative beta(exp(tH)H(Hx)). Taylor's theorem on the unoriented interval from 0 to any real s gives f(s) at most f(0)+s f'(0)+M s squared divided by two, where M=beta(u)K/2. Positivity makes this quadratic nonnegative on the entire real line. The existing quadratic discriminant theorem then gives f'(0) squared at most 2M f(0), including M=0. This proves the reverse certificate with exactly K=the operator norm of H_u squared, without division by mass or curvature. The positive-generator argument is supplied by the separate criterion below. The coefficient K is usable; no optimality claim is made.

For an arbitrary original preparation set P contained in the full positive dual, assume its finite nonnegative cone has closure equal to that dual. Finite-dimensionality identifies every original linear functional with its unique continuous-linear version. The closure is the usual topology on the original dual, not a replacement preparation set. A certificate with one fixed nonnegative q on P extends with exactly the same q to the full dual. Mathlib's weighted finite Cauchy-Schwarz inequality applies directly to signed evaluations with nonnegative weights and masses, including the empty sum. For each fixed effect the squared inequality describes a closed set of functionals, so it persists under closure.

For r strictly positive and y and r u-y in C, apply the effect certificate to y/r and use the original linear maps. Multiplication by r squared leaves exactly q r beta(y) beta(u). There is no positive lower mass bound or division by mass. The attained order-radius bound supplies a finite strictly positive r for every positive y. Therefore beta(y)=0 forces beta(Hy)=0 for every positive original beta. The symbols Certificate, Cone and Closure mean precisely this effect certificate, finite nonnegative cone and ordinary dual-topology closure.

Order-unit norm and positive-functional mass facts are classical; the construction retains the original cone, unit, functional and linear action in one construction. It asserts no literature priority or physical realization of the mathematical exponential.

**Theorem 1.2 (Cross-positivity preserves the original cone).**

$$\forall E \in Types,\; FiniteDimensionalRealNormedSpace\left(E\right) \Rightarrow \left(\forall A \in ConeUnitData\left(E\right),\; \forall L \in RealEndomorphisms\left(E\right),\; \left(\forall z \in C,\; \forall beta \in PositiveAlgebraicDual,\; beta\left(z\right) = 0 \Rightarrow 0 \le beta\left(L\left(z\right)\right)\right) \Rightarrow \left(\forall t \in NonnegativeReals,\; \forall y \in C,\; mem\left(exp\left(smul\left(t, L\right)\right)\left(y\right), C\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrderUnitNorm.cross_positive_flow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here L is any original real-linear endomorphism, C is the original closed salient convex cone containing zero, and u is its specified interior unit. The positive-dual quantifier includes every original algebraic linear functional nonnegative on C. Finite dimension supplies the unique continuous version of each such functional and completeness of the original space. No condition L(u)=0 is imposed. The exponential is precisely NormedSpace.exp of t times the continuous wrapping of that same L, in the original endomorphism algebra.

Hahn-Banach separates a boundary point z of C from its interior. The resulting nonzero functional, with its sign reversed, is nonnegative on the original cone and vanishes at z: evaluation at zero and at twice z forces the contact value to be zero. Its unit mass is strictly positive, because the already proved zero-mass bound would otherwise make the functional zero. No normalized state, self-duality or smooth boundary is assumed.

Choose a=n(Lu)+1 and d=a u-Lu. The attained order-radius inequality gives d-u in C. For y in C and epsilon strictly positive, perturb the actual orbit by w(t)=exp(tL)y+epsilon exp(a t)u. It starts in the interior and its actual derivative is Lw(t)+epsilon exp(a t)d. On a compact time interval, the closed set where w is not in the interior has a least element T if it is nonempty. Since w(0) is interior, T is strictly positive; every earlier nonnegative time is interior. Closedness of C puts w(T) in C, while the defining bad set keeps it outside the interior.

At this original boundary contact take the supporting positive beta. For negative h tending to zero with -T<h<0, beta(w(T+h)) is nonnegative and beta(w(T))=0, so the left difference quotient is nonpositive. Existence of the actual derivative gives beta(w'(T)) at most zero. Cross-positivity at the proved cone point w(T), together with beta(d) at least beta(u)>0, makes that same derivative strictly positive. This contradiction keeps every perturbed orbit interior. At each fixed nonnegative time, letting epsilon tend to zero through positive values and using closedness gives the original unperturbed orbit in C. This proof needs neither a positive Euler step nor a time-monotone orbit, and includes dimension zero and boundary initial vectors.

The classical implication is the cross-positive generator theorem of Schneider and Vidyasagar, Cross-Positive Matrices, SIAM Journal on Numerical Analysis 7(4), 508-519, Theorem 3. The original source also cites Niestegge, arXiv:1402.0158v2, Section 4, Lemma 3 for the two-sided zero-contact criterion. These mathematical sources motivate the route; the Lean proof uses the pinned Hahn-Banach, compact-minimum, exponential derivative and one-sided slope declarations directly. No literature originality is asserted.

**Theorem 1.3 (The same preparation coefficient and the same exponential).**

$$\forall E \in Types,\; FiniteDimensionalRealNormedSpace\left(E\right) \Rightarrow \left(\forall A \in ConeUnitData\left(E\right),\; \forall H \in RealEndomorphisms\left(E\right),\; \forall P \in Subsets\left(PositiveDual\right),\; \left(H\left(u\right) = 0 \land Closure\left(Cone\left(P\right)\right) = PositiveDual\right) \Rightarrow \left(\left(\left(\exists q \in R,\; 0 \le q \land \left(\forall alpha \in P,\; Certificate\left(H, q, alpha\right)\right)\right) \Leftrightarrow \left(\forall t \in R,\; \left(\forall y \in C,\; mem\left(exp\left(smul\left(t, H\right)\right)\left(y\right), C\right)\right) \land exp\left(smul\left(t, H\right)\right)\left(u\right) = u\right)\right) \land \left(\left(\forall q \in R,\; \left(0 \le q \land \left(\forall alpha \in P,\; Certificate\left(H, q, alpha\right)\right)\right) \Rightarrow \left(\left(\forall beta \in PositiveDual,\; Certificate\left(H, q, beta\right)\right) \land \left(\forall beta \in PositiveDual,\; \forall r \in PositiveReals,\; \forall y \in C,\; mem\left(sub\left(smul\left(r, u\right), y\right), C\right) \Rightarrow square\left(abs\left(beta\left(H\left(y\right)\right)\right)\right) \le q \cdot r \cdot beta\left(y\right) \cdot beta\left(u\right)\right)\right)\right) \land \left(\left(\forall t \in R,\; \left(\forall y \in C,\; mem\left(exp\left(smul\left(t, H\right)\right)\left(y\right), C\right)\right) \land exp\left(smul\left(t, H\right)\right)\left(u\right) = u\right) \Rightarrow \left(\left(\forall beta \in PositiveDual,\; Certificate\left(H, norm\left(square\left(Hu\right)\right), beta\right)\right) \land \left(\forall beta \in PositiveDual,\; \forall x \in Effects,\; square\left(abs\left(beta\left(H\left(x\right)\right)\right)\right) \le norm\left(square\left(Hu\right)\right) \cdot min\left(beta\left(x\right), beta\left(sub\left(u, x\right)\right)\right) \cdot beta\left(u\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrderUnitNorm.quantitative_generator_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume separately H(u)=0. The preparation set P is the original arbitrary subset of the full positive dual, and its finite nonnegative cone has the ordinary dual closure equal to that entire dual. Certificate(H,q,beta) means the squared effect inequality with coefficient q, every x and u-x in C, and the original evaluations beta(Hx), beta(x), beta(u). The first assertion is the full quantified equivalence between existence of one finite nonnegative preparation coefficient and positivity plus unit fixation of the same exp(tH) at every real time.

The fixed-coefficient extension and exact radius factor are retained. Their full-dual zero-contact conclusion supplies cross-positivity for H and for -H separately. The generator theorem gives each nonnegative-time semigroup. A negative time for H is a nonnegative time for -H, in the same endomorphism algebra. Independently H(u)=0 fixes the original unit. The actual inverse exp(-tH) and the canonical norm transport are those already proved above; no new cone or generator is selected.

Conversely Q=norm(H_u squared) is nonnegative and gives the certificate for every positive original functional. Applying this same bound to u-x and using H(u)=0 gives the complementary bound. Taking the lesser of the two proves the source's strengthening with Q min(beta(x),beta(u-x)) beta(u). Zero coefficient, zero mass and zero-dimensional fibers require no divisions. This theorem is a mathematical consequence for the original operator and preparations; it supplies no actual clock, reference or callable exponential.

**Theorem 1.4 (The algebraic Archimedean hypotheses supply the topology bridge).**

$$\forall E \in Types,\; FiniteDimensionalRealNormedSpace\left(E\right) \Rightarrow \left(\forall A \in ArchimedeanConeUnitData\left(E\right),\; \forall H \in RealEndomorphisms\left(E\right),\; \forall P \in Subsets\left(PositiveDual\right),\; \left(H\left(u\right) = 0 \land Closure\left(Cone\left(P\right)\right) = PositiveDual\right) \Rightarrow \left(Closed\left(C\right) \land \left(mem\left(u, Interior\left(C\right)\right) \land \left(\left(\left(\exists q \in R,\; 0 \le q \land \left(\forall alpha \in P,\; Certificate\left(H, q, alpha\right)\right)\right) \Leftrightarrow \left(\forall t \in R,\; \left(\forall y \in C,\; mem\left(exp\left(smul\left(t, H\right)\right)\left(y\right), C\right)\right) \land exp\left(smul\left(t, H\right)\right)\left(u\right) = u\right)\right) \land \left(\left(\forall q \in R,\; \left(0 \le q \land \left(\forall alpha \in P,\; Certificate\left(H, q, alpha\right)\right)\right) \Rightarrow \left(\left(\forall beta \in PositiveDual,\; Certificate\left(H, q, beta\right)\right) \land \left(\forall beta \in PositiveDual,\; \forall r \in PositiveReals,\; \forall y \in C,\; mem\left(sub\left(smul\left(r, u\right), y\right), C\right) \Rightarrow square\left(abs\left(beta\left(H\left(y\right)\right)\right)\right) \le q \cdot r \cdot beta\left(y\right) \cdot beta\left(u\right)\right)\right)\right) \land \left(\left(\forall t \in R,\; \left(\forall y \in C,\; mem\left(exp\left(smul\left(t, H\right)\right)\left(y\right), C\right)\right) \land exp\left(smul\left(t, H\right)\right)\left(u\right) = u\right) \Rightarrow \left(\left(\forall beta \in PositiveDual,\; Certificate\left(H, norm\left(square\left(Hu\right)\right), beta\right)\right) \land \left(\forall beta \in PositiveDual,\; \forall x \in Effects,\; square\left(abs\left(beta\left(H\left(x\right)\right)\right)\right) \le norm\left(square\left(Hu\right)\right) \cdot min\left(beta\left(x\right), beta\left(sub\left(u, x\right)\right)\right) \cdot beta\left(u\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrderUnitNorm.archimedean_quantitative_generator_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

ArchimedeanConeUnitData retains the original convex cone C containing zero, salience, positive unit u, and two algebraic assumptions. For each v some strictly positive real r has r u-v and r u+v in C. If v+epsilon u belongs to C for every epsilon>0, then v belongs to C. No closedness or interior-unit hypothesis is supplied in these data. An arbitrary auxiliary real norm realizes the usual finite-dimensional topology; the theorem derives the required topological facts for that topology and the same C and u.

The order-unit bounds put every v in the linear span of C, so its affine span is the whole space. The pinned finite-dimensional convex-set theorem gives nonempty interior, including dimension zero. If v is an interior point and r u-v is in C for r>0, cone addition makes r u interior, and positive inverse scaling makes u interior. For v in the closure of C, adding epsilon u puts v+epsilon u in C: addition of an open interior set absorbs closure. The original Archimedean condition then puts v in C. Thus C is closed.

The map toData preserves C and u literally and supplies only these proved topology properties. The operator H, preparation set P, all functionals, the ordinary dual closure, and the actual exponential remain the original ones. The norm, square-operator coefficient, same-K extension, exact scaling and complementary minimum are precisely those in the preceding quantified criterion. This is the source's complete mathematical Theorem 68.1. The correlated execution-map extension of Section 69.2 is a separate statement and is not a consequence claimed here.

## References

- Truth anchor: `D5/S3/Topology/OrderUnitNorm.archimedean_quantitative_generator_iff`
- Truth anchor: `D5/S3/Topology/OrderUnitNorm.cross_positive_flow`
- Truth anchor: `D5/S3/Topology/OrderUnitNorm.norm_core`
- Truth anchor: `D5/S3/Topology/OrderUnitNorm.quantitative_generator_iff`
