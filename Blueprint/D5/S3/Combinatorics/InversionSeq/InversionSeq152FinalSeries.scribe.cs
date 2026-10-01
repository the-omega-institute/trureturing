using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.InversionSeq;

internal sealed class InversionSeq152FinalSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/InversionSeq/InversionSeq152FinalSeries.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2023inversion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The final descent statistic has a generating function determined by the Catalan series.",
        H("Generating Function for the Final Descent"),
        Blocks(
            Node("inversionseq-inversionseq152finalseries-final-descent-enumeration", "Final descent weights", "final_descent_enumeration",
                "Let R be a commutative ring, q an element of R and C(x) the Catalan series with coefficients in R. Let H(x) have, as its coefficient of x to the power n, the sum of q to the power d over Dyck paths of semilength n, where d is the length of the final descent. The empty path has d equal to zero. Then (1 - q x C(x)) H(x) = 1.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
