using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackCrossingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackCrossing.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let p be a non-simple permutation in C such that every proper nontrivial interval crosses a fixed gap strictly and has minimum value greater than one. There is a proper nontrivial interval containing every such interval. Contracting it gives a simple skeleton in C occurring in p, and standardizing its entries gives a block. Inflating that skeleton by this block recovers p. If the block has length m, the skeleton has length equal to the length of p minus m plus one.",
        H("An interval crossing a fixed gap"),
        Blocks(
            Node("pop-stack-popstackcrossing-crossing-decomposition", "An interval crossing a fixed gap", "crossing_decomposition",
                "Let p be a non-simple permutation in C such that every proper nontrivial interval crosses a fixed gap strictly and has minimum value greater than one. There is a proper nontrivial interval containing every such interval. Contracting it gives a simple skeleton in C occurring in p, and standardizing its entries gives a block. Inflating that skeleton by this block recovers p. If the block has length m, the skeleton has length equal to the length of p minus m plus one.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
