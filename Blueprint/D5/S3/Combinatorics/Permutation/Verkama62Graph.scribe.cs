using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class Verkama62GraphDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/Verkama62Graph.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/verkama2026connectivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source graph and its anchored initial cycle.",
        H("The source graph and its anchored initial cycle"),
        Blocks(
            Node("verkama62-graph-valuegraph", "Value-labelled inversion graph", "valueGraph",
                "The vertices are zero-based representatives u of the values u+1. Two vertices u,v are adjacent precisely when ((u+1)-(v+1)) times ((pi inverse(u)+1)-(pi inverse(v)+1)) is negative. Both differences and the product are evaluated in the integers.", DescribeRole.Definition),
            Node("verkama62-graph-value-adj", "Order form of source adjacency", "value_adj",
                "Adjacency is equivalent to u < v with pi inverse(v) < pi inverse(u), or the reverse inequalities. Adding one to both value labels and position labels cancels in the two integer differences.", DescribeRole.Theorem),
            Node("verkama62-graph-anchored-start", "An initial cycle through both anchors", "anchored_start",
                "For every n >= 3 and permutation pi, assume that the value-labelled inversion graph is connected and remains connected after every vertex deletion. Then some triangle or 3412 starts an ear run containing both the original leftmost and bottommost points. Two distinct neighbours force the first value and the position of the minimum to be at least two in zero-based coordinates. An intermediate point below the first value yields the triangle. Otherwise positions 0,1,pi inverse(0),pi inverse(1) yield the 3412.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
