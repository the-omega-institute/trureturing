using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscentChildrenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscentChildren.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/benyi2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Appending a letter to a 210-avoiding weak ascent sequence follows the semi-Baxter succession rule.",
        H("Children of Weak Ascent Sequences"),
        Blocks(
            Node("weak-ascent-weakascentchildren-weaklabel", "The sequence label", "weakLabel",
                "Put M equal to the maximum entry, D equal to the largest inversion bottom, and H equal to one plus the number of weak ascents. The label is (M - D + 1, H - M) when the last entry equals M, and (M - D, H - M + 1) otherwise; maxima and the last entry of the empty sequence are taken as zero.", DescribeRole.Definition),
            Node("weak-ascent-weakascentchildren-childlabel", "The semi-Baxter succession rule", "childLabel",
                "A label (h, k) has children (i + 1, k + 1) for i from zero through h minus one, and (h + k - j, j + 1) for j from zero through k minus one.", DescribeRole.Definition),
            Node("weak-ascent-weakascentchildren-weak-children-rule", "Labels after appending a letter", "weak_children_rule",
                "For every nonempty 210-avoiding weak ascent sequence with label (h, k), both coordinates are positive. The letters from its largest inversion bottom through one plus its weak ascent count are in bijection with the two index ranges of the semi-Baxter succession rule, and appending each letter gives the corresponding child label.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
