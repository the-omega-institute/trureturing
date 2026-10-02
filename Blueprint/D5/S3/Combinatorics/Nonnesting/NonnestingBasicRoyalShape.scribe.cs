using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingBasicRoyalShapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingBasicRoyalShape.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity of the preceding multiplicities determines the step sequence of a doubled word.",
        H("Dyck Shape of a Doubled Word"),
        Blocks(
            Node("nonnesting-nonnestingbasicroyalshape-scan", "Occurrence-parity scan", "scan",
                "Start with a set of active letters. For each letter, record a downstep if it is active and an upstep otherwise, then toggle its membership in the active set.", DescribeRole.Definition),
            Node("nonnesting-nonnestingbasicroyalshape-shape", "Dyck shape", "shape",
                "For a word obtained by permuting a list containing two copies of each entry of a given letter list, scanning from the empty active set produces a Dyck path.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
