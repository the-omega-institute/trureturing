using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscentPermParentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscentPermParents.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/benyi2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restricting a 2-41-3-avoiding permutation to its smallest letters preserves avoidance.",
        H("Parents of Vincular-Avoiding Permutations"),
        Blocks(
            Node("weak-ascent-weakascentpermparents-restriction-avoids", "Restriction to an initial set of letters", "restriction_avoids",
                "For every permutation of one through n avoiding 2-41-3 and every nonnegative m at most n, retaining only the entries at most m gives a permutation of one through m avoiding 2-41-3.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
