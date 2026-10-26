using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PointwiseTensorRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete original pointwise tensor construction for an actual finite Kraus channel with a represented left inverse.",
        H("PointwiseTensorRecovery"),
        Blocks(Describe.Lean(
            DescribeId.Create("whole-pointwise-core-attempt"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/PointwiseTensorRecovery.whole_pointwise_core_attempt"),
            H("whole pointwise core attempt"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
            Blocks(
                Paragraph(Text("Let finite complex Kraus families E_a: C^d -> C^n and A_b: C^n -> C^d satisfy sum_a E_a* E_a = identity, sum_b A_b* A_b = identity, and sum_b A_b (sum_a E_a T E_a*) A_b* = T for every complex T. Fix v in d. The original unused parameter r in d is retained. No orthogonal syndrome decomposition, tensor isometry, normalized representation or multiplicity state is assumed.")),
                Paragraph(Text("Define N(T) = sum_a E_a T E_a*, Q = N(identity), P = spectralSupport(Q), W = spectralInverseSqrt(Q), pi(T) = W N(T) W and F(i,j) = pi(e_ij). The inverse square root has its actual value zero on the kernel. Put E0 = range(P) and K0 = range(F(v,v)). All subspace, tensor and adjoint structures are the canonical complex structures.")),
                Paragraph(Text("The whole statement produces Theta: K0 tensor C^d -> E0 as an isometric linear equivalence, B: C^n -> (d -> K0), and endomorphisms sigma and sigmaInv of K0. Its seventeen conclusions are recorded below.")),
                Paragraph(Text("(1) Theta(w tensor e_i) = F(i,v)w in C^n. (2) Theta inverse applied to x in E0 is sum_i B(x)_i tensor e_i. (3) B(y)_i = F(v,i)y in C^n. (4) Theta* is Theta inverse.")),
                Paragraph(Text("(5) jE* jE = identity and (6) jE jE* = P, where jE is the inclusion of E0 in C^n. (7) jK* jK = identity and (8) jK jK* = F(v,v), where jK is the inclusion of K0.")),
                Paragraph(Text("(9) sigma(w) = Qw as an ambient vector. (10) sigma is positive. (11) Re inner(w,sigma(w)) > 0 for every nonzero w. (12) sigma sigmaInv = identity and (13) sigmaInv sigma = identity. (14) trace(sigma) = 1.")),
                Paragraph(Text("(15) Q Theta(z) = Theta((sigma tensor identity)z). (16) For U = jE Theta and every complex matrix T, N(T) = U (sigma tensor T) U*. This factorization includes all complex matrices, with no positivity or self-adjointness restriction on T. (17) sigmaInv(w) = (W W)w in the ambient Euclidean space.")),
                Paragraph(Text("The derivation begins with Y(T) = sum_b A_b* T A_b. Scalarity of composite Kraus operators of the identity channel gives Y(T) E_a = E_a T. Conjugate transpose gives E_a* Y(T) = T E_a*. Thus Q Y(T) = Y(T) Q = N(T). Functional calculus makes Y(T) commute with W, and the actual spectral sandwich W Q W = P yields pi(T) = P Y(T). Support acts identically on each E_a and on N(T). These are the shared identities from SpectralRecoveryCorrectness.kraus_left_inverse_spectral_relations.")),
                Paragraph(Text("The identity N(T) Y(S) = N(TS), the commutation with W, and support give pi(T) pi(S) = pi(TS). The actual formula gives pi(T)* = pi(T*) and pi(identity) = P. Consequently the actual F(i,j) form matrix units. The whole proof also derives Q F = F Q, Q W W = W W Q = P and the required preservation by R = W W. Trace preservation gives trace(Q F(v,v)) = trace(N(e_vv)) = 1. Expanding an arbitrary complex T proves N(T) = Q sum_ij T(i,j) F(i,j).")),
                Paragraph(Text("PointwiseTensorGeometry.matrix_unit_pointwise_tensor now applies with these actual F, P, Q, R and N. Its explicit S/B inverse construction and verified tensor metric supply Theta and the coordinate identities. Restricting Q and W W supplies sigma and sigmaInv. The positive zero-form criterion gives strict positivity, trace cyclicity gives trace one, and the coordinate calculation yields the intertwining and factorization.")),
                Paragraph(Text("The finite reversible-channel fixed-ancilla normal form is prior literature: Nayak and Sen, Invertible Quantum Operations and Perfect Encryption of Quantum States, Theorem 2.1. The scalar Kraus and multiplicative-domain setting is also described by Choi, Johnston and Kribs. The present repository-derived proof specifies the actual spectral support, matrix-unit ranges and canonical tensor coordinates; these citations do not claim a verbatim Lean API or external novelty.")),
                Paragraph(Text("This is a pointwise result. The smooth compact constant-rank family, the global bundle and global Theta/sigma construction, ST37, ST38, ST23.2, the R-family and control obligations remain outside this theorem. In particular, no global vector frame, smooth parameter dependence, Chern obstruction, or full control protocol follows from this pointwise formalization alone."))),
            DescribeRole.Theorem))));
}
