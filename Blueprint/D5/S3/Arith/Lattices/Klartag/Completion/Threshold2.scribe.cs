using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Completion;

internal sealed class Threshold2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Completion/Threshold2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform constants and completion of lattice packing.",
        H("Threshold2"),
        Blocks(
            Paragraph(Text("Uniform constants and completion of lattice packing. The results below relate threshold2 to the stochastic ellipsoid construction.")),
            Node("claim-2", "smallConst", "small Const",
                "Final.smallConst at the new threshold.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
