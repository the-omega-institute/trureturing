using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BurriReversePolarDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/BurriReversePolar.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact radical rotations for the active reverse source matrix.",
        H("The explicit right-polar blocks"),
        Blocks(
            Paragraph(Text("Set s = sqrt(11), t = sqrt(10), D(l) = sqrt((l s + 3t)^2 + (s-t)^2), c(l) = (l s + 3t)/D(l), and k(l) = (s-t)/D(l). The two coupled blocks use l = 4 and l = 2. The remaining block is t times the matrix with diagonal 3 and off-diagonal -1. The active source matrix is Y diag(s,t,t,s,t,t)/62.")),
            Entry("unitary", "actual_unitary", "The fixed radical unitary",
                "Both exact radical parameter pairs satisfy the unit-circle equation. The active matrix U therefore satisfies both complex unitary identities, and both sine parameters are strictly positive."),
            Entry("positive", "actual_polar_positive", "A positive source polar product",
                "The literal active product M U is positive semidefinite. Each coupled block is symmetric with positive first diagonal entry and determinant (3l-1)s t. Unnormalized Hadamard columns reconstruct the complete six-dimensional product as a sum of positive congruences."),
            Entry("svd", "active_svd", "A literal nonnegative SVD",
                "The Hermitian spectral decomposition of the positive product supplies two unitary factors and nonnegative singular values. Their source-ordered adjoints multiply to the explicit active rotation. This statement concerns the active block; its full source padding is a further identification."),
            Entry("gap", "actual_polynomial_gap", "The fixed positive polynomial gap",
                "The exact radical parameters discharge every premise of the sum-of-squares positivity statement. This is an algebraic certificate; an actual decoder fidelity comparison additionally requires the canonical-purification and ordinary Petz identities."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
