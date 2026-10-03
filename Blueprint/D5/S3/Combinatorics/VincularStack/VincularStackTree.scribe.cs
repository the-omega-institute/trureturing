using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.VincularStack;

internal sealed class VincularStackTreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/VincularStack/VincularStackTree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/zhao2024vincular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximum deletion and insertion give an invertible generating tree with the Schroeder succession rule.",
        H("The Generating Tree of Sortable Permutations"),
        Blocks(
            Node("vincularstack-vincularstacktree-parentsiteequiv", "The parent and insertion site correspondence", "parentSiteEquiv",
                "For every nonnegative n, pairs consisting of a sortable permutation of one through n and a gap at which inserting n plus one remains sortable correspond bijectively to sortable permutations of one through n plus one. The forward map inserts the new maximum; the inverse deletes it and records its position.", DescribeRole.Definition),
            Node("vincularstack-vincularstacktree-activesites", "Active insertion sites", "activeSites",
                "For a word and an entry M, the active sites are the gaps from zero through the word length at which inserting M produces an SC output avoiding 231.", DescribeRole.Definition),
            Node("vincularstack-vincularstacktree-earlier-site-activity", "Activity at an earlier site", "earlier_site_activity",
                "Let a word have distinct entries, let M exceed them all, and let L exceed M. Suppose insertion of M at a later gap is sortable, and an earlier gap is positive. Inserting L at the earlier gap after that insertion remains sortable if and only if inserting L there in the original word is sortable and its original output gap is at most that of the later gap.", DescribeRole.Theorem),
            Node("vincularstack-vincularstacktree-succession-rule", "The Schroeder succession rule", "succession_rule",
                "Let a word of distinct entries have an SC output avoiding 231, and let M and L satisfy that M exceeds every word entry and L exceeds M. Write k for the number of active sites for M. The positive active sites admit a bijective ranking from zero through k minus two. Inserting M at the beginning gives k plus one active sites for L; insertion at a positive site of rank r gives r plus three active sites for L. Thus a label k has child labels from 3 through k, followed by two copies of k plus one, whenever k is at least two.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
