using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class OctahedronBlockDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/OctahedronBlock.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The octahedral block and its full finite counts.", H("The octahedral block and its full finite counts"),
        Blocks(
            Node("octahedron", "The actual octahedral graph", "octahedron", "The graph is the complete equipartite graph on Fin 3 times Fin 2. Two vertices are adjacent exactly when their first coordinates differ. Thus the graph is finite, simple, undirected and loopless, with six vertices.", DescribeRole.Definition),
            Node("octahedron-block", "Exact counts and no isolated vertices", "octahedron_block", "The conjunction states that the actual vertex type has cardinality six, the complete family of inclusion-minimal nonempty forts has cardinality eleven, the full rooted choice family has cardinality twelve, and every vertex has a neighbor. Kernel reduction checks every subset, including all possible proper fort subsets. This is a fixed-block ingredient, with no arbitrary-multiplicity or asymptotic conclusion.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
