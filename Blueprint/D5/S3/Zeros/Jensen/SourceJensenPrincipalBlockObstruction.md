# Literal Jensen Principal-Block Obstruction

## Abstract

Fixed literal Jensen coefficients obstruct unchanged positive principal extensions.

P_d is sourceJensenPolynomial d, with the actual coefficients a(k)=sourceThetaMoment(k)/(2k)! and density Phi(x)/Re(xiReading(1/2)). Q(A)=det(I+X A) is the complex matrix pencil polynomial, with entries embedded as constant polynomials. It is distinct from the infinite reflected xi series. A hat on C_w denotes the real forbiddenPartition polynomial mapped coefficientwise to Complex. Fin n has indices 0 through n-1.

**Theorem 1.1 (The four edge coefficients).**

$$\begin{aligned}\forall d\in \mathbb{N},d\ge 1:\operatorname{coeff}(P_{d},0)=a_{0}\land \operatorname{coeff}(P_{d},1)=a_{1}\\\land \operatorname{coeff}(P_{d},d+1)=0\land \operatorname{coeff}(P_{d},d)=\frac{d!}{d^{d}}a_{d}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_coeff_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The independent finite sum has falling-factorial weights. The constant and linear coefficients are a(0) and a(1); the next coefficient vanishes. The leading weight is d!/d^d. Real a(k) are embedded in Complex here.

**Theorem 1.2 (Matching fixes normalization and trace).**

$$\forall d\in \mathbb{N},d\ge 1:K\in \mathbb{C}^{(d)\times (d)},Q(K)=P_{d}\implies a_{0}=1\land \operatorname{Tr}(K)=a_{1}\land (\forall k\in \mathbb{N}:0< a_{k})$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_matching_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No positivity assumption on K is needed for this bridge. The constant determinant coefficient is one and its linear coefficient is the trace. The literal raw-moment bounds then determine the actual positive denominator and all positive coefficients from a(0)=1.

**Theorem 1.3 (Strictly positive leading coefficient).**

$$\forall d\in \mathbb{N},d\ge 1:a_{0}=1\implies 0< \operatorname{coeff}(P_{d},d)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_leading_coefficient_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient is (d!/d^d)a(d), with all factors strictly positive. The displayed complex inequality uses the real-axis order: the coefficient has zero imaginary part and strictly positive real part. Both obstruction proofs obtain a(0)=1 from exact matching before applying this result.

**Theorem 1.4 (Collapse at fixed trace).**

$$\begin{aligned}\forall d\in \mathbb{N},K\in \mathbb{C}^{(d)\times (d)},H\in \mathbb{C}^{(d+1)\times (d+1)},e:\operatorname{Fin}(d)\to \operatorname{Fin}(d+1):\\\operatorname{Injective}(e)\land \operatorname{PosSemidef}(H)\land H[e,e]=K\land \operatorname{Tr}(H)=\operatorname{Tr}(K)\implies\\\exists q:\operatorname{Sum}(\operatorname{Fin}(d),\operatorname{Fin}(1))\equiv \operatorname{Fin}(d+1),(\forall i\in \operatorname{Fin}(d):q(\operatorname{inl}(i))=e(i))\\\land H_{r,r}=0\land (\forall i\in \operatorname{Fin}(d):H_{e(i),r}=0\land H_{r,e(i)}=0)\\\land H[q,q]=\operatorname{diag}(K,0)\land Q(H)=Q(K)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.fixed_trace_principal_collapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here r=q(inr(0)), and Sum is the disjoint sum of index types. The equivalence q extends the given injection itself. Equal traces make the unique complement diagonal zero. The zero-weight support-face theorem for its diagonal projection annihilates both new row and column. Thus the reindexed matrix is exactly diag(K,0), where the zero block has size one, and the determinant polynomial is unchanged. These hypotheses are consistent, for example for zero extensions; the argument does not use a contradiction or source polynomial matching.

**Theorem 1.5 (No adjacent unchanged exact models).**

$$\begin{aligned}\forall d\in \mathbb{N},d\ge 1:\neg \exists K\in \mathbb{C}^{(d)\times (d)},H\in \mathbb{C}^{(d+1)\times (d+1)},e:\operatorname{Fin}(d)\to \operatorname{Fin}(d+1):\\\operatorname{PosSemidef}(K)\land \operatorname{PosSemidef}(H)\land \operatorname{Injective}(e)\land H[e,e]=K\land Q(K)=P_{d}\land Q(H)=P_{d+1}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_principal_block_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This holds for every positive degree and every injective principal inclusion. Both exact matches fix the trace at a(1). The generic collapse keeps the determinant unchanged, while coefficient d+1 vanishes in P_d and is nonzero in P_(d+1). Its positivity is derived from the literal moments and the matching constant coefficient. No independent analytic or normalization premise is present, and no existence of either model is asserted.

**Theorem 1.6 (No unchanged family).**

$$\begin{aligned}\neg \exists (K_{d}),(e_{d}):\forall d\in \mathbb{N},d\ge 1:\\\operatorname{PosSemidef}(K_{d})\land \operatorname{Injective}(e_{d})\land K_{d+1}[e_{d},e_{d}]=K_{d}\land Q(K_{d})=P_{d}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_unchanged_family_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quantified family has K_d a complex Fin d by Fin d matrix and e_d:Fin d -> Fin(d+1) for every natural d. Exact matching and unchanged inclusion are required for every d>=1. Applying the adjacent obstruction at d=1 already contradicts such a family.

**Theorem 1.7 (Matching fixes the actual weight sum).**

$$\forall d\in \mathbb{N},d\ge 1:w\in \mathbb{R}^{2d-1},(\forall j:w_{j}\ge 0)\land \widehat{C_{w}}=P_{d}\implies a_{0}=1\land \sum_{j=0}^{2d-2}w_{j}=a_{1}\land (\forall k\in \mathbb{N}:0< a_{k})$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_chain_matching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the actual determinant identity for L_w^T L_w. Coefficient zero fixes a(0), and coefficient one together with cyclic trace gives the displayed total weight. The normalized coefficient signs follow from the literal analytic bounds. Nonnegative weights include zero and repeated weights.

**Theorem 1.8 (No unchanged exact chain extension).**

$$\begin{aligned}\forall d\in \mathbb{N},d\ge 1:\neg \exists w\in \mathbb{R}^{2d-1},u\in \mathbb{R}^{2d+1}:\\(\forall j:w_{j}\ge 0)\land (\forall j:u_{j}\ge 0)\land (\forall 0\le j< 2d-1:u_{j}=w_{j})\land \widehat{C_{w}}=P_{d}\land \widehat{C_{u}}=P_{d+1}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_unchanged_weights_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two exact matches give the same total a(1). An unchanged numerical prefix forces the appended weights u(2d-1) and u(2d) to zero. The actual bidiagonal matrix becomes diag(L_w,0), and two endpoint recurrences give C_u=C_w. The strictly positive next source coefficient contradicts that equality. This also covers d=1 and singular chains.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.fixed_trace_principal_collapse`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_chain_matching`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_coeff_edges`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_leading_coefficient_pos`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_matching_normalization`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_principal_block_obstruction`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_unchanged_family_obstruction`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.source_jensen_unchanged_weights_obstruction`
- Dependency: [D5/S3/Quantum/FockSpace/ForbiddenNeighbourTraceExtension](../../Quantum/FockSpace/ForbiddenNeighbourTraceExtension.md)
- Dependency: [D5/S3/QuantumStates/ZeroWeightSupportFace](../../QuantumStates/ZeroWeightSupportFace.md)
- Dependency: [D5/S3/Zeros/Jensen/SourceThetaMomentBounds](SourceThetaMomentBounds.md)
