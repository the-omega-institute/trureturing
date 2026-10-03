using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingBasicRoyalDownSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalDownSeries.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The downstep-weighted generating function satisfies a quadratic equation.",
        H("Quadratic Equation for Downstep Weights"),
        Blocks(
            Node("nonnesting-nonnestingbasicroyaldownseries-down-series-quadratic", "Downstep series equation", "downSeries_quadratic",
                "Let D be the ordinary generating function whose coefficient of x to the power n is the downstep weight sum at semilength n. Then 1 - (1 + x)D + 2xD squared equals zero.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
