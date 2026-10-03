using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingBasicRoyalAugCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalAugCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An extra factor records a singleton first component of a weighted Dyck path.",
        H("Augmented Dyck Weights"),
        Blocks(
            Node("nonnesting-nonnestingbasicroyalaugcount-augmented-weight", "Augmented weight sum", "augmentedWeight",
                "For semilength n, sum two to the power of the number of adjacent downstep pairs plus the number of singleton components after the first component. Multiply each summand by two when the path is nonempty and its first primitive component is a single upstep followed by a downstep.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
