using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingFourPrimitiveTwoInsertDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveTwoInsert.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The 21321 insertion preserves the four-pattern avoidance class.",
        H("Avoidance after Two-Prefix Insertion"),
        Blocks(
            Node("nonnesting-nonnestingfourprimitivetwoinsert-two-insert", "Two-prefix insertion preserves avoidance", "two_insert",
                "If an avoider begins with one, replacing its start by 21321 and shifting the remaining letters by two yields an avoider of size two greater.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
