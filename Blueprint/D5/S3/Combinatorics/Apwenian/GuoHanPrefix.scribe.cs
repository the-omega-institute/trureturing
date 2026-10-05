using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Apwenian;

internal sealed class GuoHanPrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Apwenian/GuoHanPrefix.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/guo2025apwenian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finiteness of the alphabet forces an apwenian substitution fixed point to begin with one, an even letter and one.",
        H("The Initial Parity Pattern"),
        Blocks(
            Node("guo-han-prefix-initial-prefix", "The forced initial pattern", "initial_prefix",
                "Let Sigma be a finite alphabet of nonnegative integers in which every odd letter equals one. Let p be an integer at least two, let sigma assign a word of length p to each nonnegative integer, and let a take values in Sigma and satisfy a(np + r) = sigma(a(n), r) for all nonnegative n and all r from zero through p minus one. If a is apwenian, then a(1) has image zero modulo two and a(2) = 1. Since a(0) = 1, the initial parity pattern is 101. The conclusion does not require every word assigned by sigma to every letter of Sigma to remain in Sigma.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
