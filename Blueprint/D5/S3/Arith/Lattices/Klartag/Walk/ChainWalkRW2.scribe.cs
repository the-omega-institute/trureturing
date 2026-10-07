using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class ChainWalkRW2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/ChainWalkRW2.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Chain Walk RW2"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate chain walk rw2 to the stochastic ellipsoid construction.")),
            Node("claim-2", "chainRaw2_of_walkRW2", "chain Raw2 of walk RW2",
                "ChainRaw2RW2 from the chain, with w = intWeight and tail discharged. The thirteen remaining arguments are §5 arithmetic and the chain's own lattice data.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
