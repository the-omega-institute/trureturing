using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenThirteen;

internal sealed class FishburnBasicComponentCutsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicComponentCuts.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direct-sum boundaries correspond to the ends of indecomposable permutation components.",
        H("Counting Component Boundaries"),
        Blocks(
            Node("fishburnbasiccomponentcuts-component-boundary-count", "The number of separating cuts", "component_boundary_count",
                "Let parts be a list of nonempty sum-indecomposable permutations, each on the integers from one through its length, and let p be their iterated direct sum. Among the positions from zero through the length of p, the number of cuts for which every entry before the cut is less than every entry after it is the number of parts plus one. Both endpoint cuts are included.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
