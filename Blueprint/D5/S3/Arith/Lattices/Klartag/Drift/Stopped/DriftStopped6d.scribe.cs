using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift.Stopped;

internal sealed class DriftStopped6dDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6d.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stopped log determinant drift and integrability estimates.",
        H("Drift Stopped6d"),
        Blocks(
            Paragraph(Text("Stopped log determinant drift and integrability estimates. The results below relate drift stopped6d to the stochastic ellipsoid construction.")),
            Node("claim-2", "c3eta_le", "c3eta le",
                "x := c₃''·η ≤ 2/√√n — the slack term is decreasing, like n^{−1/4}.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
