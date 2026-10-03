using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowThirtyTwoOneThreeGapCodeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowThirtyTwoOneThreeGapCode.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selected last-cycle letters divide the complementary prefix into independent value intervals.",
        H("Encoding the Value Gaps"),
        Blocks(
            Node("arrow-thirty-two-gap-data", "Selected letters and prefix", "GapData",
                "A gap datum on 1 through n consists of k strictly increasing selected letters and a complementary prefix with closed edges; together the two words permute the entire interval.", DescribeRole.Definition),
            Node("arrow-thirty-two-join-gap", "Inserting the first selected letter", "joinGap",
                "Choose an initial avoiding word of length i and a gap datum on the remaining translated values. Placing the first selected letter after that initial interval gives a gap datum with one more selected letter.", DescribeRole.Definition),
            Node("arrow-thirty-two-join-gap-bijective", "Unique first-gap decomposition", "joinGap_bijective",
                "For every n and k, this first-gap insertion is bijective: the first selected letter determines the initial interval and the translated remainder uniquely.", DescribeRole.Theorem),
            Node("arrow-thirty-two-gap-card", "Counting gap data", "gapData_card",
                "The number of gap data with k selected letters among n plus k values equals the coefficient of x to the n in the (k plus one)st power of the avoidance series.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
