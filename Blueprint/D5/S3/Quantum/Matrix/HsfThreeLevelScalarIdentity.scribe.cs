using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfThreeLevelScalarIdentityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex PSD3 cubic geometry and exact scalar coefficients.",
        H("HsfThreeLevelScalarIdentity"),
        Blocks(
            Entry("p396_identity", "p396 identity",
                "Exact P396 factorization: p396=pqr Q^2(p-q)^2(q-r)^2(r-p)^2 positiveCertificate. The proof uses elementary-symmetric identities and Newton-sum decompositions of the positive certificate.", DescribeRole.Theorem),
            Entry("p396_nonneg", "p396 nonneg",
                "The actual P396 polynomial is nonnegative for every positive triple, including collisions.", DescribeRole.Theorem),
            Entry("p396_pos", "p396 pos",
                "The actual P396 polynomial is strictly positive at pairwise distinct positive levels.", DescribeRole.Theorem),
            Paragraph(Text("The statements concern the explicitly defined closed algebraic kernels. "
                + "The commutant equality classification, identification with the original integrals, "
                + "dominated differentiation and original HSF derivative/source bridge remain outside these results. "
                + "No assertion about arbitrary matrix dimension or literature novelty follows.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsfthreelevelscalaridentity-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
