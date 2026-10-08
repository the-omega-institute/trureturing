using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift;

internal sealed class LogDetVarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/LogDetVariance.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second order log determinant bounds and accumulated drift.",
        H("Log Det Variance"),
        Blocks(
            Paragraph(Text("Second order log determinant bounds and accumulated drift. The results below relate log det variance to the stochastic ellipsoid construction.")),
            Node("claim-1", "opNorm_inv_le", "op Norm inv le",
                "‖A⁻¹‖_op ≤ 1/m from the state bounds.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
