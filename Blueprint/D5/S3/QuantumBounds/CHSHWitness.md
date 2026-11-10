# A Tight CHSH Witness

## Abstract

A normalized Bell state and fixed Pauli observables attain the positive Tsirelson value.

**Theorem 1.1 (The square root normalization is nonzero).**

$$(\sqrt{2} : \mathbb{C}) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.complex_sqrt_two_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive real square root of two remains nonzero in the complex numbers.

**Theorem 1.2 (The inverse square root normalization).**

$$((\sqrt{2} : \mathbb{C})^{-1}) \cdot ((\sqrt{2} : \mathbb{C})^{-1}) = (2 : \mathbb{C})^{-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.complex_sqrt_two_inv_mul_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the complex numbers, the product of two inverses of the positive real square root of two is the inverse of two. This is the normalization factor for the Bell density matrix.

The classical comparison uses four measurable sign-valued random variables on one probability space whose law is independent of the settings. The commutative CHSH inequality bounds the absolute value pointwise by two. Integrating with respect to that same probability law gives the bound for the four correlations; finite support is not required. The Bell witness uses the Pauli Z and X observables and their normalized sum and difference to attain twice the square root of two.

For finite local positive operator-valued measurements, summing the joint trace probabilities over the second outcome replaces its effects by the identity. The first marginal therefore depends only on the first effect and the common density matrix, independently of the second setting. The argument uses normalization of each local measurement and a shared quantum state, and does not require a shared classical table of answers for all incompatible settings.

**Theorem 1.3 (The Bell density is a normalized positive state).**

$$\operatorname{PosSemidef}(\rho_{Bell}) \land \operatorname{tr}(\rho_{Bell})=1$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.bell_density_is_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized Bell vector defines a rank-one positive semidefinite density matrix. Its trace is one.

**Theorem 1.4 (Bob's fixed observables are self-adjoint involutions).**

$$\forall j\in\{0,1\},\ B_j^{*}=B_j \land B_j^{2}=I$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.bob_observables_are_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bob's sum and difference of the Pauli Z and X matrices, each divided by square root two, are self-adjoint and square to the identity.

**Theorem 1.5 (The Kronecker operator equals the lifted CHSH combination).**

$$S=A_0^{L}B_0^{L}+A_0^{L}B_1^{L}+A_1^{L}B_0^{L}-A_1^{L}B_1^{L}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.chsh_operator_eq_lifted_chsh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lift Alice's observables by tensoring on the right with the identity, and Bob's by tensoring on the left. The original sum of Kronecker products is exactly the CHSH combination of these lifted matrices; the superscript L denotes this lift.

**Theorem 1.6 (The lifted observables satisfy the CHSH tuple conditions).**

$$\operatorname{IsCHSHTuple}(A_0^{L},A_1^{L},B_0^{L},B_1^{L})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.lifted_observables_form_chsh_tuple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four lifted observables are self-adjoint involutions in the two-qubit matrix algebra. Each lifted Alice observable commutes with each lifted Bob observable, as required by IsCHSHTuple.

**Theorem 1.7 (The Bell witness attains the positive Tsirelson value).**

$$\operatorname{tr}(\rho_{Bell} S)=2\sqrt{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CHSHWitness.bell_chsh_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A0 be the Pauli Z matrix and A1 the Pauli X matrix. Let B0 be the sum of Pauli Z and Pauli X divided by square root two, and let B1 be their difference divided by square root two. The named matrix S is the CHSH combination of the four corresponding Kronecker products. The state rhoBell is the rank-one density matrix obtained by flattening the existing bellCoefficients matrix and normalizing it by square root two.

The checked trace is exactly positive two times square root two. The companion Lean certificate bell_density_is_state proves that rhoBell is positive semidefinite with trace one, while bob_observables_are_valid proves that B0 and B1 are self-adjoint involutions. Thus the equality is a qualified state-observable witness, not an unnormalized matrix identity.

Mathlib's tsirelson_inequality is the upstream source for the general CHSH upper bound. This declaration establishes only its explicit finite-dimensional tightness witness: it introduces no operator norm, eigenvalue classification, spectral order, C-star matrix instance, or second proof of the upper bound.

A two-axis application uses the same Bell projector and computational reference. Let n and m be real unit Bloch vectors, c their inner product, d its absolute value, and assume d is strictly less than one. For every positive complex four-by-four matrix rho of trace one, put q = Re tr(rho W) and f = Re tr(rho Phi), where Phi is bellDensity. The transpose below is in the basis defining Phi. All expectations use this one density matrix; independently chosen conditional sources do not satisfy this premise.

$$
C_v=\operatorname{kronecker}\left(\operatorname{transpose}\left(\operatorname{B}\left(v\right)\right), \operatorname{B}\left(v\right)\right), W=C_n+C_m
$$

Choose s = 1 when c is nonnegative and s = -1 otherwise, and put k = n cross m. For a real vector a, O(a) is the outer product of vec(B(a)) with its conjugate. The existing B_formula_core fixes every matrix entry. Pauli multiplication gives B(v)B(a)B(v) = B(2 inner(v,a) v - norm(v)^2 a); Matrix.kronecker_mulVec_vec transfers this equality to the original tensor space. Expanding the same entries, using only the two unit-norm identities, gives the following slack identity. In the negative-c case replace m by -m: its correlation matrix and O(k) are unchanged. No rotation or replacement of the Bell reference is required.

$$
(1-d)(2dI+2(1-d)\phi-W)=dO(n-sm)+O(k)
$$

Both outer products are positive by Matrix.posSemidef_vecMulVec_self_star. Since d is nonnegative and 1-d is positive, PosSemidef.add and PosSemidef.smul make the slack positive. Apply RHLinalg.trace_mul_nonneg_of_posSemidef to this slack and the actual rho. Trace linearity and trace rho = 1 give q <= 2d + 2(1-d)f. Applying the same trace theorem to rho and Phi gives f >= 0. Division by the positive number 2(1-d) yields the full lower envelope.

$$
f\geq\operatorname{max}\{0,1-\frac{2-q}{2(1-d)}\}
$$

The feasible interval is exactly [-2,2]. For a unit axis, C is a Hermitian involution, so I+C and I-C are positive: each is half the product of I+C or I-C with its conjugate transpose. Taking their expectations in rho gives each single-axis correlation in [-1,1], hence q in [-2,2]. The states below realize every point of this interval, so this condition is also sufficient.

The upper Bell-orthogonal endpoint is sigmaPlus = O(n+s m)/(4(1+d)). Its denominator is the squared length of vec(B(n+s m)); hence it is positive with trace one. Tracelessness of B makes its Bell overlap zero, and the Pauli reflection formula gives W sigmaPlus = 2d sigmaPlus. The lower endpoint is sigmaMinus = O(k)/(2(1-c^2)). The cross-product norm identity gives trace one and positivity, while orthogonality of k to both axes gives W sigmaMinus = -2 sigmaMinus and zero Bell overlap. These formulas include c = 0 and either sign of c; the strict nonparallel condition keeps both denominators positive.

For 2d <= q <= 2, use rho = t Phi + (1-t) sigmaPlus with t = (q-2d)/(2(1-d)). The weights lie in [0,1], q is the prescribed expectation, and f = t. For -2 <= q <= 2d, use rho = t sigmaPlus + (1-t) sigmaMinus with t = (q+2)/(2+2d); then the expectation is q and f = 0. Positivity and trace one follow from the same convex-sum APIs. Thus the lower envelope is attained for every feasible q, including its endpoints, and is optimal when only q is retained.

For separable mixed states reuse the Bloch product-state estimate followed by convexity: q <= 1+d. An actual maximizing separable state is gamma-transpose tensor gamma, where u = (n+s m)/sqrt(2(1+d)) and gamma = (I+B(u))/2. The norm identity makes u unit, scalarB_posSemidef_iff gives positivity of gamma, and tracelessness of B gives trace one. Transpose and Kronecker positivity give an actual product density. Its expectation is inner(n,u)^2 + inner(m,u)^2 = 1+d. Therefore epsilon = 2-q < 1-d excludes separability. This comparison uses the original transpose convention on the first factor.

This is application exposition of finite Pauli algebra, outer-product positivity, trace positivity and convex mixtures; it supplies no additional named Lean theorem. The kernel statements cited by the Describe nodes above retain their own scope. The complete arbitrary-axis statement and its calibration clauses are not asserted to have a frozen covering declaration. Trusted effects and eta parameters, the raw-correlator-to-calibrated-correlator relation, estimated-error bounds and their 1/eta amplification, and transverse reconstruction with 1/sqrt(1-c^2) amplification require separate verification. The feasible-state construction supplies no preparation procedure, no menu classification or common-source theorem, and no optimality claim when further conditional tomography is used.

## References

- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.bell_chsh_value`
- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.bell_density_is_state`
- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.bob_observables_are_valid`
- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.chsh_operator_eq_lifted_chsh`
- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.complex_sqrt_two_inv_mul_self`
- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.complex_sqrt_two_ne_zero`
- Truth anchor: `D5/S3/QuantumBounds/CHSHWitness.lifted_observables_form_chsh_tuple`
- Dependency: [D5/S3/Quantum/QubitWitnesses](../Quantum/QubitWitnesses.md)
