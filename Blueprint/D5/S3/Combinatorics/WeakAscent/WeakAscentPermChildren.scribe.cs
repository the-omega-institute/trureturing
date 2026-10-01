using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscentPermChildrenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscentPermChildren.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/benyi2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permutations avoiding 2-41-3 have the semi-Baxter succession rule.",
        H("Children of Vincular-Avoiding Permutations"),
        Blocks(
            Node("weak-ascent-weakascentpermchildren-permlabel", "The permutation label", "permLabel",
                "For a permutation p of one through n, its label (h, k) has h equal to the number of active insertion sites strictly after the position of n and k equal to the number of positions whose entries exceed all earlier entries. Positions and insertion sites are numbered from zero.", DescribeRole.Definition),
            Node("weak-ascent-weakascentpermchildren-permutation-children-rule", "Labels after inserting the maximum", "permutation_children_rule",
                "For every nonempty permutation of one through n avoiding 2-41-3 with label (h, k), both coordinates are positive. The permutations obtained by inserting n + 1 at an active site are in bijection with the two index ranges of the semi-Baxter succession rule, and each resulting permutation has the corresponding child label.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
