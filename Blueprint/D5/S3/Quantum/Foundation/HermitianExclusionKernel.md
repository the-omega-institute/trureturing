# Full Hermitian exclusion and orthogonal support

## Abstract

In the complete complex positive semidefinite cone, exclusion by any proper real-linear effect equals the density face annihilating the confirmed unit vector.

Let J be any finite index type with decidable equality. The carrier is the real inner product space of all complex Hermitian matrices indexed by J. Its cone consists of all positive semidefinite matrices, and its unit is the trace. The normalized base contains every positive semidefinite trace-one matrix. Effects range over every real-linear functional f satisfying 0 <= f(Y) <= trace(Y) for every positive semidefinite Y. No selected measurements or restricted effect domain is used.

**Definition 1.1 (The entire positive semidefinite cone).**

Lean statement: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.cone`

*Formalization.* `D5/S3/Quantum/Foundation/HermitianExclusionKernel.cone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cone is PointedCone.positive on the original Hermitian carrier, with its Loewner order.

**Definition 1.2 (The original trace unit).**

Lean statement: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.unit`

*Formalization.* `D5/S3/Quantum/Foundation/HermitianExclusionKernel.unit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unit is the real-linear pairing with the identity matrix. HermitianMat.one_inner identifies it with the trace on every Hermitian matrix.

**Theorem 1.3 (Every positive original functional has a positive representative).**

Lean statement: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.positive_representative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/HermitianExclusionKernel.positive_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real-linear functional nonnegative on the entire native PSD cone is pairing with a PSD Hermitian matrix on the entire carrier. The original Riesz proof tests every native outer product. This same declaration supplies the whole-effect model application of the original state-cover theorem.

**Theorem 1.4 (The entire exclusion is an orthogonal support face).**

Lean statement: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.exclusion_iff_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/HermitianExclusionKernel.exclusion_iff_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex Euclidean vector v of norm one and every Hermitian matrix X, X belongs to the original exclusion of rankOne(v) if and only if X is positive semidefinite, trace(X)=1, and Xv=0. The exclusion quantifies over every original proper real-linear effect f, with f(rankOne(v))=1 and f(X)=0. X may have any rank, and there is no prior choice of an orthogonal face or compressed coordinate domain.

Finite-dimensional real Riesz representation writes the chosen functional as pairing with a Hermitian matrix A. Testing positivity on every outer product shows A is positive semidefinite; the upper trace bound similarly shows I-A is positive semidefinite. Acceptance of the unit vector makes (I-A)v=0, hence Av=v. Zero pairing of A and X puts the support of A in the kernel of X. Since v is in the range of A, Xv=0. This argument uses the whole mixed matrix X without replacing it by a rank-one state. Conversely, pairing with rankOne(v) is an original proper functional by positivity and the trace-product bound; it accepts rankOne(v) and vanishes on X when Xv=0.

For the original qutrit application, fix a finite dimensional real normed V and ONE real-linear equivalence Phi: Herm_3(ℂ) -> V with Phi(PSD)=C and u(Phi(Y))=Tr(Y) for EVERY Hermitian Y. Set K={x in C:u(x)=1}, P=ext(K), and let E be ALL real-linear f with 0<=f<=u on the entire C. These are exactly CircuitBalancedConfirmation.base, pure and proper. Write f_A(x)=<A,Phi inverse(x)>, using the real Hermitian trace pairing. HermitianExclusionKernel.positive_representative and HermitianMat.nonneg_iff_inner_nonneg identify E bijectively with 0<=A<=I: apply positivity separately to f and u-f; inner-product nondegeneracy gives uniqueness. Composition with Phi and its inverse transports the complete confirming fibers and exclusions in both directions. Phi is onto the whole carrier, not just a readout subspace.

Fix any unit complex v, put P_v=vv*, Q=I-P_v and p=Phi(P_v). The whole confirmer fiber F_p={f in E:f(p)=1} is exactly {f_(P_v+B):0<=B<=Q}. Indeed positivity of I-A and <I-A,P_v>=0 imply (I-A)v=0 by Matrix.PosSemidef.dotProduct_mulVec_zero_iff; hence AP_v=P_vA=P_v and QAQ=A-P_v. HermitianMat.conj_nonneg gives A-P_v>=0, while A<=I gives A-P_v<=Q. Conversely 0<=B<=Q forces Bv=0 by HermitianMat.ker_antitone, so P_v+B is an effect confirming p. For EVERY mixed x=Phi(X) in K, <B,X> >= 0 and B=0 is allowed. Thus the attained minimum of the entire F_p is e_p(x)=<P_v,X>, literally FacetZeroGluing.comparison C u p x; HermitianExclusionKernel.exclusion_iff_kernel identifies D_p with ALL PSD trace-one X satisfying Xv=0.

The separate common family A_p={f in F_p:f|D_p=0}, defined by OrthogonalJointCompletion.common, is the singleton {e_p}. If a residual B above is nonzero, Tr(B)>0 by HermitianMat.trace_pos and X=B/Tr(B) is an actual member of D_p. Vanishing there gives <B,B>/Tr(B)=0, so B=0 by inner_self_eq_zero. Conversely the attained-minimum inequality makes e_p zero on every D_p. The same residual argument applied to any PSD trace-one X with <P_v,X>=1 gives X-P_v>=0 with trace zero; HermitianMat.le_trace_smul_one forces X=P_v. Consequently the entire one-value face of e_p is {p}, including all mixed states, and g=u-e_p vanishes on the cone exactly on the nonnegative p ray.

The original state norm is FixedZeroObstruction.stateNorm, the norm of stateReadout on the WHOLE compact K: ||f_A||_K=max_(x in K)|f_A(x)|=||A||_op for every Hermitian A. Here ||.||_op is the Euclidean matrix operator norm of Matrix.Norms.L2Operator. IsSelfAdjoint.le_algebraMap_norm_self and IsSelfAdjoint.neg_algebraMap_norm_le_self bound A between +/-||A||_op I, giving the upper inequality on every density matrix. ContinuousLinearMap.norm_eq_iSup_rayleighQuotient and Matrix.l2_opNorm_toEuclideanCLM give the reverse inequality by testing the actual normalized rank-one matrices zz*/||z||^2 for all nonzero z. This identifies the norm of differences of arbitrary effects as well; the Frobenius norm is not substituted.

Let B(p)=FixedZeroObstruction.zeroEffects C u p, the ENTIRE proper-effect fiber vanishing at p. For any other pure q=Phi(P_w), every A representing a member of B(p) satisfies AP_v=P_vA=0. Put R=I-P_w. The actual repair A'=RAR satisfies 0<=A'<=R<=I and A'w=0, by HermitianMat.conj_nonneg and HermitianMat.conj_mono. Since A=QAQ, the exact identity RAR-A=(R-Q)AR+QA(R-Q), together with ||A||_op,||Q||_op,||R||_op<=1, gives ||A'-A||_op<=2||P_w-P_v||_op using norm_add_le and norm_mul_le. Interchanging p and q repairs EVERY member of the other fiber. Both fibers contain zero; their stateReadout images are compact, as closed subsets of the finite dimensional compact effect interval. Metric.hausdorffDist_le_of_mem_dist applied to both directed pointwise distance bounds gives d_H(B(p),B(q))<=2||P_w-P_v||_op in the exact original state norm. Phi inverse and the finite dimensional matrix norm are continuous, so this bound gives Hausdorff continuity along EVERY original pure sequence. Closedness of C and strict positivity of u provide compact K via CircuitBalancedConfirmation.base_compact; they hold in the native PSD/trace model and transport through this same Phi.

These are applications and deductions from the existing frozen kernel, SectionROGFrame rank-one APIs and FixedZeroObstruction stateReadout/stateNorm/zeroEffects definitions, together with the Mathlib APIs named above at pinned revision 56a005855ea17e0b0958f73ec801ae140b0a1679. The whole pure carrier, all original charts, full normal compression and exact original lifting cost are continued in HermitianExclusionBall, OriginalNormalRestriction and UnitPreservingLiftImage. The application adds no mathematical declaration or physical preparation, instrument, dynamics or literature-priority assertion.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.cone`
- Truth anchor: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.exclusion_iff_kernel`
- Truth anchor: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.positive_representative`
- Truth anchor: `D5/S3/Quantum/Foundation/HermitianExclusionKernel.unit`
- Dependency: [D5/S3/Quantum/Foundation/FacetZeroGluing](FacetZeroGluing.md)
- Dependency: [D5/S3/Quantum/Foundation/SectionROGFrame](SectionROGFrame.md)
