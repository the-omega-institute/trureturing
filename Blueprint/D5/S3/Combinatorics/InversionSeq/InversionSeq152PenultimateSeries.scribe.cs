using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152PenultimateSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152PenultimateSeries.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The weight of the penultimate descent has a generating function expressed through final descent weights.",
        H("Generating Function for the Penultimate Descent"),
        Blocks(
            Node("inversionseq-inversionseq152penultimateseries-penultimate-descent-enumeration", "Weighted penultimate descents", "penultimate_descent_enumeration",
                "Let R be a commutative ring and w a function from nonnegative integers to R with w(0) = 0. Write C(x) for the Catalan series. In degree n, let P(x) sum w of the penultimate nonempty descent length over Dyck paths of semilength n, using length zero when there are fewer than two descents. Let F(x) sum w of the final descent length, using zero for the empty path. Then (1 - x) P(x) = x C(x) F(x).", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
