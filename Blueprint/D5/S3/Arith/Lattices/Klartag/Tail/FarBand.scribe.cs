using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Tail;

internal sealed class FarBandDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Tail/FarBand.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice tail bounds along the matrix walk.",
        H("Far Band"),
        Blocks(
            Paragraph(Text("Lattice tail bounds along the matrix walk. The results below relate far band to the stochastic ellipsoid construction.")),
            Node("claim-4", "integrand_le", "integrand le",
                "Φ(y)·(1 − y·s)^{−c} ≤ e^{b·y − a·y²}/(√(2π)·Y₀) on y ≥ Y₀ > 0 with y·s ≤ 1/2, b = c·s, a = 1/2 − c·s².", DescribeRole.Theorem),
            Node("claim-5", "far_le", "far le",
                "The far-band bound. Y₀ is the split point, Y₁ the reach endpoint.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
