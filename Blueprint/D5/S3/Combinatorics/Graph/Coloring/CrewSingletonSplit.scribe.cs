using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Coloring;

internal sealed class CrewSingletonSplitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Coloring/CrewSingletonSplit.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/GraphColoring/crew2026dichromatic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A beta-integral estimate bounds the singleton-split coefficient.",
        H("Positive singleton-split coefficients"),
        Blocks(
            Node("weight", "weight", "The weight of a marked split",
                "For a finite set of other blocks with natural sizes, a natural marked block size r, "
                + "and a real palette parameter x, start with the falling factorial of x − 1 of length "
                + "equal to the number of other blocks. Subtract the sum over subsets of other blocks. "
                + "Each summand is the falling factorial of x of length equal to the number of blocks "
                + "outside the subset, multiplied by the factorial of the subset size and its alternating "
                + "sign, and divided by r plus the sum of the sizes in the subset.",
                DescribeRole.Definition),
            Node("weight-bounds", "weight_bounds", "A positive lower bound",
                "If the marked block has at least two elements, every other block has positive size, "
                + "and x is at least the total size minus one, the weight is at least the falling "
                + "factorial of x − 1 of length equal to the number of other blocks divided by x + 1. "
                + "The weight is strictly positive. A beta-moment identity turns the signed sum into "
                + "an integral. A product estimate bounds that integral on the unit interval.",
                DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
