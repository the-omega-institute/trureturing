# Invertible physical scaling and native Gramian limit

## Abstract

Invertible physical scaling and native Gramian limit

**Theorem 1.1 (Invertible physical scaling and native Gramian limit).**

$$(\forall 0<T, d\left(T\right)e\left(T\right)=I_{U} \land e\left(T\right)d\left(T\right)=I_{U} \land e\left(T\right)G\left(T\right)e\left(T\right)=\int_{0}^{1} Z\left(T, s\right)^{*}Z\left(T, s\right) ds)\\{}\land (\forall x\in U,x\neq 0\Rightarrow 0<\langle x,H\left(x\right)\rangle)\\{}\land (\exists R\ge 0, \forall T, (0<T\le 1 \land T\left\lVert b \right\rVert<1) \Rightarrow \left\lVert e\left(T\right)G\left(T\right)e\left(T\right)-H \right\rVert\le RT)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/DerivativeLayerNativeGramian.derivative_layer_native_gramian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be an arbitrary finite-dimensional real inner-product space, and W an arbitrary complete real inner-product space. Let B:V→V and C:V→W be arbitrary linear maps. Neither observability of the whole V nor a positive dimension is assumed.

Put n=dim V, N(j)=the intersection of ker(C B^k) for 0≤k<j, U=N(n) orthogonal complement, E(j)=N(j) intersect N(j+1) orthogonal complement for 0≤j<n. Pi(j):V→V is the actual orthogonal projection onto E(j). All n layer indices are retained, even when their layer is zero. Write b and c for the continuous linear maps associated to B and C; i:U→V is the inclusion. All norms are induced Hilbert operator norms.

On U let Q(j) be Pi(j) restricted to U, with its range returned to U by the orthogonal projection onto U. Put d(T)=sum sqrt(T) T^j Q(j) and e(T)=sum (sqrt(T) T^j)^(-1) Q(j). Define A(t)=c exp(t b) i and G(T)=the interval integral from zero to T of A(t) adjoint composed with A(t).

Put P(s)=sum over j<n of s^j/j! c b^j Pi(j) i and H=the interval integral from zero to one of P(s) adjoint composed with P(s). Write Z(T,s)=sqrt(T) A(T s) e(T). Composition is written by juxtaposition in the display, and a star denotes the Hilbert adjoint.

For every T>0, d(T)e(T) and e(T)d(T) both equal the identity on U, and e(T)G(T)e(T) equals the integral of Z(T,s) adjoint composed with Z(T,s). H has positive quadratic form at every nonzero state. There is R≥0 for which the linear error holds whenever 0<T≤1 and T times the norm of b is less than one.

Projection orthogonality gives the inverse equations without a rank premise. The physical change of variables t=T s and self-adjointness of the scaling give the integral identity. Uniform normalized-trajectory convergence controls the difference of the two squared operators and its integral.

For the observable Euclidean application, fix arbitrary d,p≥1 and matrices B∈R^(d×d), C∈R^(p×d) with (C,B) observable, and use their associated linear maps on V=R^d and W=R^p. The derivative filtration in `D5/S3/Observer/Linear/DerivativeLayerNormalizedObservation.derivative_layer_normalized_observation` has N(d)=0, so U is the whole state space. Let m be the least j with N(j+1)=0; then 0≤m<d. For j>m, N(j)=0 and E(j)=0. Thus the supplier sums over j<d reduce exactly to j=0,...,m, retaining every layer in that range and the actual exponential trajectory.

The finite orthogonal decomposition R^d=the orthogonal sum of E(j), 0≤j≤m, supplies a subordinate orthonormal basis e_i. The upstream subordinateOrthonormalBasis and subordinateOrthonormalBasisIndex construction, followed by reindexing with Tuple.sort, orders the layer labels w_i increasingly. Each e_i belongs to E(w_i), and #{i:w_i=j}=d_j=dim E(j) for every 0≤j≤m, including zero-dimensional groups. Fix any such ordered subordinate basis for all subsequent identities and estimates; no choice of minimal layers or subordinate basis imposes an additional hypothesis on B or C.

Let S have columns e_i in standard coordinates. The operator G(T) above has standard matrix G_standard(T)=the integral from zero to T of exp(t Bᵀ) Cᵀ C exp(t B), and matrix G_L(T)=Sᵀ G_standard(T) S in this basis. For x=sum x_j with x_j∈E(j), P(s)x=sum s^j C B^j x_j/j!, with j=0,...,m. If P_L(s) has columns P(s)e_i, put M_L=the integral from zero to one of P_L(s)ᵀ P_L(s). Thus M_L is the matrix of the constant limit operator H above in the same basis. Since S is orthogonal, these coordinate changes preserve the Euclidean operator norm and the spectrum, and det G_L(T)=det G_standard(T) because det(S)^2=1.

For T>0 the physical scaling D_T=d(T) acts on E(j) by sqrt(T) T^j=T^(j+1/2). Its matrix is D(T)=diag(sqrt(T) T^(w_i)), and e(T) is its two-sided inverse. Write H(T)=D(T)^(-1) G_L(T) D(T)^(-1) for the normalized matrix family, distinguishing it from the constant operator H above. The exact identity is G_L(T)=D(T) H(T) D(T). All short-time estimates fix B,C, the Euclidean norms, the time unit and the chosen basis, and take T down to zero through positive values.

For x_j∈E(j), C B^k x_j=0 when k<j. The exact factorial Taylor estimate in `D5/S3/Observer/Linear/ExactTaylorObservationRemainder.norm_observation_taylor_remainder` gives, for some fixed K₀≥0 and δ>0, the operator norm bound ‖sqrt(T) C exp(Ts B) D_T^(-1)-P(s)‖≤K₀ T simultaneously for every 0<T<δ and s∈[0,1]. Integrating the difference of the squared operators gives ‖H(T)-M_L‖≤K T for fixed K≥0 after shrinking δ. The supplier conditions T≤1 and T‖B‖<1 are ensured, for example, by also taking δ≤min(1,1/(1+‖B‖)). Hence H(T) tends to this same M_L along nhdsWithin(0,Ioi(0)), in the induced Euclidean operator norm.

Positivity of the same M_L follows from `D5/S3/Observer/Linear/DerivativeLayerGramianPositivity.derivative_layer_gramian_pos`: zero polynomial energy makes every coefficient C B^j x_j vanish; then x_j belongs both to N(j+1) and its orthogonal complement, so each x_j=0. Separately, for every T>0, `D5/S3/Observer/Linear/ObservableTrajectoryCoordinates.observable_trajectory_coordinates` identifies the actual physical Gramian with F*F for the injective trajectory map F:x↦(t↦C exp(t B)x) in L²(0,T). Thus G(T), G_standard(T) and G_L(T) are positive definite for every positive T, providing positivity of the same congruence used below.

Choose a fixed μ>0 with xᵀ M_L x≥μ‖x‖². For sufficiently small positive T the norm error is at most μ/2, so a I≼H(T)≼b I with fixed a=μ/2>0 and b=‖M_L‖+μ/2>0. Congruence by the same D(T) gives a D(T)^2≼G_L(T)≼b D(T)^2. Equivalently, for every state x, a‖D_T x‖²≤⟨x,G(T)x⟩≤b‖D_T x‖². Taking a common smaller positive radius preserves all these bounds. The right-sided convergence, positive M_L, increasing w_i and positive actual congruence are exactly the inputs of `D5/S3/Observer/Linear/GradedCongruenceSpectrum.graded_congruence_spectrum`; its application below gives every sorted spectral index and every layer group.

The same multiplicities give q=sum_i(2w_i+1)=sum over j=0,...,m of (2j+1)d_j. For every T>0, det(D(T)^2)=the product of T^(2w_i+1)=T^q, and the exact congruence yields det G_standard(T)=det G_L(T)=T^q det H(T). Determinant is a C¹ polynomial on this fixed finite matrix space, hence locally Lipschitz at this same M_L. Combining that local bound with ‖H(T)-M_L‖≤K T gives fixed K_det≥0 and δ_det>0 with |det H(T)-det M_L|≤K_det T for 0<T<δ_det.

In particular |det G_standard(T)/T^q-det M_L|≤K_det T. With r(T)=det H(T)-det M_L, the same actual Gramian satisfies det G_standard(T)=T^q(det M_L+r(T)), |r(T)|≤K_det T, so det G_standard(T)=T^q(det M_L+O(T)). The leading coefficient is the positive determinant of the literal integral of P_L(s)ᵀ P_L(s) in the fixed subordinate orthonormal basis. Orthogonal invariance also identifies it with the determinant of the polynomial-limit operator in standard coordinates.

Two-oscillator modal application. In the energy coordinates x=(q1,p1,q2,p2), take B=diag(J2,2 J2), with J2=[[0,1],[-1,0]], and energy ||x||²/2. This is the constant coordinate change x=L z, L=diag(1,1,2,1), from Poisson matrix diag(J2,J2) and positive energy matrix diag(1,1,4,1): LᵀL is that energy matrix and L diag(J2,J2) Lᵀ=B. The transformed generator is the same B, since L diag(J2,J2) diag(1,1,4,1) L⁻¹=B.

For C_sum, the ordered orthonormal layer vectors are (1,0,1,0)/sqrt(2), (0,1,0,2)/sqrt(5), (1,0,-1,0)/sqrt(2), and (0,2,0,-1)/sqrt(5), with weights (0,1,2,3). For C_sep they are the coordinate vectors in the order (q1,q2,p1,p2), with weights (0,0,1,1). For every natural j, the actual derivative kernel N(j) is the span of vectors whose weight is at least j, and E(j) is the span of vectors whose weight equals j. Thus the cumulative ranks are (0,1,2,3,4) and (0,2,4), the last layer indices are 3 and 1, and the nonzero layer dimensions are (1,1,1,1) and (2,2), respectively. Both finite jets are injective.

In these actual layer coordinates, P_sum(s)=(2/sqrt(2),5s/sqrt(5),3s²/(2sqrt(2)),s³/sqrt(5)) and P_sep(s)=[[1,0,s,0],[0,1,0,2s]]. These are obtained from the orthogonal projections onto the derivative layers, with coefficients C B^j/j!. Entrywise application of the scalar monomial integral identifies the integrals of P(s)ᵀP(s). For the sum sensor the integral is R diag(a) H3 diag(a) R, where R=diag(1/sqrt(2),1/sqrt(5),1/sqrt(2),1/sqrt(5)), a=(2,5,3/2,1), and H3 has entries 1/(i+j+1), for i,j=0,...,3. For the split sensor it is [[1,0,1/2,0],[0,1,0,1],[1/2,0,1/3,0],[0,1,0,4/3]].

The determinant of the four-row Taylor matrix with rows C_sum B^j/j! is 3/2, det H3=1/6048000, and the determinants of the two actual polynomial integrals above are 1/2688000 and 1/36. For every T>0 the same physical Gramian satisfies det G_sum(T)/T^16=det H_sum(T) and det G_sep(T)/T^8=det H_sep(T), where H(T)=D(T)^(-1)SᵀG(T)S D(T)^(-1) in the corresponding fixed basis. The sum-side physical determinant limit and all sorted eigenvalue bounds additionally require transporting the generic normalized-operator estimate through these explicit coordinates.

For nonzero real frequency omega, put B_omega=[[0,omega],[-omega,0]] and C_omega=(1,0). The real regular representation of complex multiplication transports the complex exponential to exp(t B_omega)=[[cos(omega t),sin(omega t)],[-sin(omega t),cos(omega t)]]. Thus the literal sensor Gramian is the integral of the outer product (cos(omega t),sin(omega t)) with itself; this identifies it with the physical exponential-integral definition. The exponential transport applies Mathlib’s NormedSpace.map_exp and Algebra.leftMulMatrix_complex.

Entrywise integration gives G_omega(T)=[[T/2+sin(2 omega T)/(4 omega),(1-cos(2 omega T))/(4 omega)],[(1-cos(2 omega T))/(4 omega),T/2-sin(2 omega T)/(4 omega)]]. Its determinant is (T²-sin²(omega T)/omega²)/4. These identities hold for every real T whenever omega is nonzero. The entries use the existing integral_cos_sq, integral_sin_sq and integral_sin_mul_cos₂ formulas.

The limits sin(u)/u→1, (1-cos(u))/u²→1/2 and (u-sin(u))/u³→1/6 give det G_omega(T)/T⁴→omega²/12 as T decreases to zero through positive values. For example, factor u²-sin²(u)=(u-sin(u))(u+sin(u)), with u=omega T; this preserves the frequency factor in the coefficient. The two residual limits follow by applying HasDerivAt.lhopital_zero_nhdsNE to the existing trigonometric derivatives and sin(u)/u limit.

For the actual split sensor C_sep=[[1,0,0,0],[0,0,1,0]], the same physical exponential and integral give G_sep(T)=diag(G_1(T),G_2(T)) in the ordered coordinates (q1,p1,q2,p2). Determinants therefore multiply, and det G_sep(T)/T⁸→(1/12)(4/12)=1/36. Both C_sep and C_sum=(1,0,1,0) have Tr(CᵀC)=2.

This modal computation establishes the physical split-sensor determinant and its leading coefficient. Information, Bayes risk over all measurable estimators, arbitrary positive noise schedules, and the optional finite-moment experiment also require their corresponding Gaussian and asymptotic interfaces; the modal calculation alone does not establish those conclusions.

The finite derivative filtration supplies orthogonal geometry, while the exponential power series and Bochner integral supply the analytic operations.

## References

- Truth anchor: `D5/S3/Observer/Linear/DerivativeLayerGramianPositivity.derivative_layer_gramian_pos`
- Truth anchor: `D5/S3/Observer/Linear/DerivativeLayerNativeGramian.derivative_layer_native_gramian`
- Truth anchor: `D5/S3/Observer/Linear/DerivativeLayerNormalizedObservation.derivative_layer_normalized_observation`
- Truth anchor: `D5/S3/Observer/Linear/ExactTaylorObservationRemainder.norm_observation_taylor_remainder`
- Truth anchor: `D5/S3/Observer/Linear/GradedCongruenceSpectrum.graded_congruence_spectrum`
- Truth anchor: `D5/S3/Observer/Linear/ObservableTrajectoryCoordinates.observable_trajectory_coordinates`
- Dependency: [D5/S3/Observer/Linear/DerivativeLayerGramianPositivity](DerivativeLayerGramianPositivity.md)
- Dependency: [D5/S3/Observer/Linear/DerivativeLayerNormalizedObservation](DerivativeLayerNormalizedObservation.md)
