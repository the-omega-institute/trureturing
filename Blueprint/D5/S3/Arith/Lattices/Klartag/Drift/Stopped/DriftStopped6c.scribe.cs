using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift.Stopped;

internal sealed class DriftStopped6cDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/Stopped/DriftStopped6c.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stopped log determinant drift and integrability estimates.",
        H("Drift Stopped6c"),
        Blocks(
            Paragraph(Text("Stopped log determinant drift and integrability estimates. The results below relate drift stopped6c to the stochastic ellipsoid construction.")),
            Node("claim-4", "sq_eq_qrt", "sq eq qrt",
                "n² = q^8 for q = √√n.", DescribeRole.Theorem),
            Node("claim-5", "cube_eq_qrt", "cube eq qrt",
                "n³ = q^12 for q = √√n.", DescribeRole.Theorem),
            Node("claim-6", "c3eta_le", "c3eta le",
                "x ≤ 2/√√n. c₃''·η ≤ q^11·√2/q^12 = √2/q. So x → 0 like n^{−1/4}.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
