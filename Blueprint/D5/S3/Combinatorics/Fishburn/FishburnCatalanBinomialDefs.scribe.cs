using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnCatalanBinomialDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnCatalanBinomialDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binomial transform of the Catalan numbers enumerates two classes of pattern-avoiding Fishburn permutations.",
        H("The Binomial-Catalan Enumeration"),
        Blocks(
            Node("fishburncatalanbinomialdefs-binomial-catalan", "The binomial-Catalan sum", "binomialCatalan",
                "For every nonnegative integer n, the binomial-Catalan sum is the sum over k from one through n of the binomial coefficient choosing k minus one from n minus one multiplied by the Catalan number of index n minus k. The sum is zero when n is zero.", DescribeRole.Definition),
            Node("fishburncatalanbinomialdefs-claim1013", "The two avoidance classes", "claim1013",
                "For every positive integer n, the number of Fishburn permutations of length n avoiding 2413 and 2431 and the number avoiding 2431 and 3241 both equal the binomial-Catalan sum at n.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
