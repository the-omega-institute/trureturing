using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class FailTotalBound99Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/FailTotalBound99.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Fail Total Bound99"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate fail total bound99 to the stochastic ellipsoid construction.")),
            Node("claim-1", "numSteps_le", "num Steps le",
                "N ≤ 16·n⁷·log n + 1 — numStepsAdopted2 is a Nat.ceil.", DescribeRole.Theorem),
            Node("claim-2", "poly_le", "poly le",
                "The polynomial factor of the two exponential terms is at most 173·n¹⁰.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
