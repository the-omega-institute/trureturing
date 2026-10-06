using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.State;

internal sealed class RawDataInstRW2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/State/RawDataInstRW2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric matrix state invariants and padded driving laws.",
        H("Raw Data Inst RW2"),
        Blocks(
            Paragraph(Text("Symmetric matrix state invariants and padded driving laws. The results below relate raw data inst rw2 to the stochastic ellipsoid construction.")),
            Node("claim-1", "rawData_of_latticeR", "raw Data of lattice R",
                "RawDataR, eight numeric fields proved. The seven q/W/A₀ fields are hypotheses, as in RawDataInst.rawData_of_lattice; R is Klartag's (1−1/n)/α.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
