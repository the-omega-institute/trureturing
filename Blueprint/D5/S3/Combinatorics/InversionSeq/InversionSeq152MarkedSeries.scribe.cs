using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152MarkedSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152MarkedSeries.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sum of weights on interior descents is related to the weight on the final descent.",
        H("Generating Function for a Marked Interior Descent"),
        Blocks(
            Node("inversionseq-inversionseq152markedseries-marked-interior-descent-enumeration", "Weighted interior descents", "marked_interior_descent_enumeration",
                "Let R be a commutative ring and w a function from nonnegative integers to R with w(0) = 0. Write C(x) for the Catalan series. In degree n, let M(x) sum, over Dyck paths of semilength n, the weights w of the lengths of all nonempty descents except the last, and let F(x) sum the weight w of the final descent length. The empty path has final descent length zero. Then (2 - C(x)) M(x) = (C(x) - 1) F(x).", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
