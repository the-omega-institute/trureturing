using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class ActualSpectralWhiteningDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/SpectralTopology/ActualSpectralWhitening.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Smooth actual spectral functions at constant PSD rank",
        H("Smooth actual spectral functions at constant PSD rank"),
        Blocks(
            Paragraph(Text("The result concerns the actual functional-calculus support, inverse square root with value zero on the kernel, and nonnegative square root of a smooth positive semidefinite matrix family whose rank is constant. The manifold, matrix size and rank are arbitrary; compactness, nonempty base and positive rank are not required. A global eigenbasis and smoothness of the spectral functions are not supplied as inputs.")),
            Paragraph(Text("The Hermitian square map has the existing derivative V mapped to YV+VY and is smooth. At a positive definite Y, the existing Traces.jordan_conjugation and Traces.diagonal_conjugated_jordan give positive coefficients lambda(i)+lambda(j), so this derivative is a continuous linear equivalence. The inverse function theorem supplies a smooth local inverse. The identities sqrt(X squared)=X on a positive definite neighborhood and square(sqrt(A))=A identify that local inverse with the actual CFC square root. Continuity of the square root is not assumed in this identification.")),
            Paragraph(Text("For a constant-rank PSD family, selected independent columns C of Q give a local Gram projection C(C* C) inverse C*. Equality of symmetric projections on the actual Euclidean range identifies this projection with spectralSupport Q. This gives smoothness of the specified support. With P that support, H=Q+1-P is positive definite. Functional calculus gives W=P(sqrt(H)) inverse and sqrt(Q)=P sqrt(H). Smooth inversion and the positive definite root result then prove the entire spectral triple.")),
            Paragraph(Text("The statement allows moving ranges. For example, a positive scalar times the projection onto the rotating unit vector (cos(t),sin(t)) is a rank-one family in dimension two; the range varies although its rank is constant. The zero family is also in scope with rank zero. These examples explain applicability and do not add instance theorems or numerical certificates.")),
            Paragraph(Text("The proof reuses HermitianCubeDerivative.square_hasFDerivAt and square_contDiff, ProjectionRange smooth matrix operations and the existing local Gram certificate. The imported cube-root theorem is a different matrix function; this result proves smoothness of the specified square root. This is a classical analytic construction, with no claim of literature novelty.")),
            Paragraph(Text("The six public targets have unfinished four-slot escape audits tracked at https://github.com/the-omega-institute/trureturing/issues/18787. No compiled registration or declared_validated status is asserted. The actual input-first Choi rank, full tensor atlas application, global Theta and inverse, sigma and W squared restrictions, decoder, root-column family and Stinespring realization remain separate original ST37 obligations. This analytic endpoint does not settle original8340 or its parent atoms.")),
            Describe.Remark(
                DescribeId.Create("actualspectral-herm"),
                DeclarationHandle.Create(Prefix + "Herm"),
                H("Herm"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Herm n is the real self-adjoint submodule of complex Fin n square matrices, with the inherited norm and real linear structure.")))),
            Describe.Lean(
                DescribeId.Create("actualspectral-positive-hermitian-sqrt-contdiffat"),
                DeclarationHandle.Create(Prefix + "positive_hermitian_sqrt_contDiffAt"),
                H("positive_hermitian_sqrt_contDiffAt"),
                StatementSource.FromAuthor(Formula("PositiveHermitianData", "SmoothHermitianRoot")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("PositiveHermitianData is the complete original input: an arbitrary natural n, A in the real self-adjoint submodule of complex Fin n square matrices, and a proof that A.val is positive definite. SmoothHermitianRoot means ContDiffAt over R of smooth order top, at A, of X mapped to CFC.sqrt(X.val), valued in the ambient matrix space."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualspectral-support-range"),
                DeclarationHandle.Create(Prefix + "support_range"),
                H("support_range"),
                StatementSource.FromAuthor(Formula("PSDMatrixData", "ActualSupportRange")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("PSDMatrixData consists of arbitrary n, a complex Fin n square matrix Q and its positive-semidefiniteness proof. ActualSupportRange means the conjunction: the Euclidean linear ranges of spectralSupport Q and Q agree; spectralSupport Q is Hermitian; and spectralSupport Q squared equals itself."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualspectral-actual-constant-rank-support-smooth"),
                DeclarationHandle.Create(Prefix + "actual_constant_rank_support_smooth"),
                H("actual_constant_rank_support_smooth"),
                StatementSource.FromAuthor(Formula("ConstantRankPSDData", "SmoothSupport")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ConstantRankPSDData contains all original quantified inputs: arbitrary types E,H,B, a real normed additive model E, topologies on H and B, a charted-space structure, I a real model with corners, an IsManifold I infinity B instance, arbitrary natural n and r, Q from B to complex Fin n square matrices, ContMDiff I of smooth order infinity of Q, positive semidefiniteness at every point, and matrix rank Q(x)=r at every point. SmoothSupport means ContMDiff I of smooth order infinity of x mapped to spectralSupport(Q(x)), in the same ambient matrix space."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualspectral-positive-matrix-sqrt-smooth"),
                DeclarationHandle.Create(Prefix + "positive_matrix_sqrt_smooth"),
                H("positive_matrix_sqrt_smooth"),
                StatementSource.FromAuthor(Formula("PositiveFamilyData", "SmoothRoot")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("PositiveFamilyData contains arbitrary E,H,B, the same real manifold structures and smoothness order as ConstantRankPSDData, arbitrary natural n, a smooth ambient matrix family Q, and positive definiteness of every Q(x). It assumes no constant rank separately. SmoothRoot means ContMDiff I of smooth order infinity of x mapped to the actual CFC.sqrt(Q(x))."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualspectral-actual-whitening-extension"),
                DeclarationHandle.Create(Prefix + "actual_whitening_extension"),
                H("actual_whitening_extension"),
                StatementSource.FromAuthor(Formula("PSDMatrixData", "ExtensionIdentities")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For q in PSDMatrixData, define P=spectralSupport Q and H=Q+1-P. ExtensionIdentities is exactly H.PosDef and spectralInverseSqrt Q=P*(CFC.sqrt H) inverse and CFC.sqrt Q=P*CFC.sqrt H, where inverse is the matrix inverse. These values include the kernel of Q."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualspectral-actual-constant-rank-whitening-smooth"),
                DeclarationHandle.Create(Prefix + "actual_constant_rank_whitening_smooth"),
                H("actual_constant_rank_whitening_smooth"),
                StatementSource.FromAuthor(Formula("ConstantRankPSDData", "SmoothSpectralTriple")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For q in ConstantRankPSDData, SmoothSpectralTriple is exactly the conjunction of real ContMDiff I, smooth order infinity, of spectralSupport composed with Q, spectralInverseSqrt composed with Q, and CFC.sqrt composed with Q, all valued in the ambient complex matrix space. No additional premises are packaged into this predicate."))),
                DescribeRole.Theorem)),
        []));

    private static StrataLint.Scribe.Formula Formula(string domain, string conclusion) =>
        F.Disp(F.Seq(F.Forall, F.Sp, F.Id("q"), F.InMacro, F.Sp, F.Id(domain),
            F.Comma, F.Sp, new StrataLint.Scribe.Formula.Apply(F.Id(conclusion), [F.Id("q")]), F.Dot));
}
