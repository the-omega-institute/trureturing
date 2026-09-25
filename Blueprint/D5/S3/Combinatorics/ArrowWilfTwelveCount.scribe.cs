using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowWilfTwelveCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowWilfTwelveCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Decorated data insert decreasing lower entries around an upper permutation skeleton, giving avoiders with a prescribed largest fixed point.",
        H("Decorated Objects for the First Pattern"),
        Blocks(
            Node("full-support", "The standard support", "fullSupport", "The support consists of the natural numbers from one through n.", DescribeRole.Definition),
            Node("lower-support", "Entries below m", "lowerSupport", "The lower support consists of the natural numbers from one through m minus one.", DescribeRole.Definition),
            Node("upper-support", "Entries above m", "upperSupport", "The upper support consists of the natural numbers from m plus one through n.", DescribeRole.Definition),
            Node("fixed-gap-labels", "Gaps forced positive", "fixedGapLabels", "The labels are precisely upper-skeleton values outside K whose hat cycle is a singleton; their following gaps must be positive.", DescribeRole.Definition),
            Node("twelve-data", "Decorated data for a largest fixed point", "TwelveData", "The data choose k upper values K, a word on the full upper support whose exact fixed-point set is the complement of K, a bound requiring that complement to have at most m minus one values, and a gap vector of total m minus one that is positive at those fixed-point labels.", DescribeRole.Definition),
            Node("lower-descending", "The decreasing lower word", "lowerDescending", "The list contains m minus one down through one, in decreasing order.", DescribeRole.Definition),
            Node("twelve-list", "The decorated output word", "twelveList", "Interleave successive blocks of the decreasing lower word after the chosen upper skeleton, with an initial block before m and m immediately before the first upper entry.", DescribeRole.Definition),
            Node("twelve-list-permutation", "The output uses each value once", "twelveList_perm", "For one at most m at most n, the decorated output permutes the standard support from one through n.", DescribeRole.Theorem),
            Node("twelve-list-fixed-m", "The distinguished value is fixed", "twelveList_fixed_m", "Under the support bounds, hat fixes m in the decorated output.", DescribeRole.Theorem),
            Node("twelve-list-no-upper-fixed", "No upper value remains fixed", "twelveList_no_upper_fixed", "Each upper singleton block receives a lower entry after it, while non-singleton blocks remain non-singleton; hence no value greater than m is hat-fixed.", DescribeRole.Theorem),
            Node("twelve-list-avoids", "The decorated output avoids the first pattern", "twelveList_avoids", "The output avoids (12; 3 to 3): all lower entries are decreasing and there is no fixed point above m.", DescribeRole.Theorem),
            Node("twelve-word", "An avoiding word with largest fixed point", "twelveWord", "The decorated list is packaged as a word on the full support that avoids the first pattern and has largest hat-fixed value m.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
