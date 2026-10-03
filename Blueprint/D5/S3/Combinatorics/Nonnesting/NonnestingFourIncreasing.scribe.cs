using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingFourIncreasingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingFourIncreasing.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent letters and value cuts constrain increasing-order avoiders.",
        H("Structure with Increasing First Occurrences"),
        Blocks(
            Node("nonnesting-nonnestingfourincreasing-increasing-adjacent", "Adjacent positions of consecutive letters", "increasing_adjacent",
                "In an increasing-order avoider, the second occurrence of i and the first occurrence of i plus one occupy adjacent positions.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingfourincreasing-increasing-prefix", "The first three letters", "increasing_prefix",
                "For size at least two, an increasing-order avoider begins either 112 or 121.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingfourincreasing-increasing-cut-iff", "Cut criterion for consecutive letters", "increasing_cut_iff",
                "In an increasing-order avoider, a value cut at i occurs exactly when the second i precedes the first i plus one.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
