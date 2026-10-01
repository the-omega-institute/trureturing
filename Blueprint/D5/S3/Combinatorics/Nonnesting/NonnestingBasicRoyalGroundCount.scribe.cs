using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingBasicRoyalGroundCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalGroundCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent downsteps and later singleton components contribute to the same weight.",
        H("Combined Dyck Weights"),
        Blocks(
            Node("nonnesting-nonnestingbasicroyalgroundcount-ground-weight", "Combined weight sum", "groundWeight",
                "For semilength n, sum over all Dyck paths two to the power of the number of adjacent downstep pairs plus the number of ground-level singleton components after the first component.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
