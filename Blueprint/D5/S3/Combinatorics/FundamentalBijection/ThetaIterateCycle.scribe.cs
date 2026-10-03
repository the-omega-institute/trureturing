using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateCycleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycle.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A parameter permutation specifies a long cycle and a sequence of cyclic successors.",
        H("A Distinguished Cycle from a Parameter Word"),
        Blocks(
            Node("fundamental-bijection-thetaiteratecycle-p", "The distinguished long-cycle permutation", "P",
                "For a parameter word r of length h, take the inverse fundamental image of the word h plus two, followed by the letters of r each increased by one, followed by one.", DescribeRole.Definition),
            Node("fundamental-bijection-thetaiteratecycle-b", "The successor word of the parameter", "b",
                "For each x from one through the length of r, record one plus the letter following x in r, or one if x is the last letter.", DescribeRole.Definition),
            Node("fundamental-bijection-thetaiteratecycle-b-perm-of-first-max", "The successor word is a permutation", "b_perm_of_first_max",
                "If r is a permutation beginning with its maximum, its successor word b(r) permutes the same interval of integers.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
