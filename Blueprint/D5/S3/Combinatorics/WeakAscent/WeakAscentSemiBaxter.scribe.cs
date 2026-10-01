using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscentSemiBaxterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscentSemiBaxter.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/benyi2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weak ascent sequences avoiding 210 are counted by the semi-Baxter numbers.",
        H("Equinumerosity with Semi-Baxter Permutations"),
        Blocks(
            Node("weak-ascent-weakascentsemibaxter-permextensions", "Permutation extensions", "permExtensions",
                "The extensions of a word p at depth d are the permutations of one through the length of p plus d avoiding 2-41-3 whose restriction to entries at most the length of p equals p.", DescribeRole.Definition),
            Node("weak-ascent-weakascentsemibaxter-result", "The weak ascent and semi-Baxter enumeration", "result",
                "For every nonnegative n, the number of 210-avoiding weak ascent sequences of length n equals the number of permutations of one through n avoiding the vincular pattern 2-41-3.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("benyi-mansour-ramirez-weak-ascent-210"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
