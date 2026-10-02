using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscentCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscentCounting.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/benyi2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The semi-Baxter succession rule counts extensions of 210-avoiding weak ascent sequences.",
        H("Counting Weak Ascent Extensions"),
        Blocks(
            Node("weak-ascent-weakascentcounting-treecount", "Descendants in the labelled tree", "treeCount",
                "The number T(d, h, k) is one at depth zero. At depth d + 1 it is the sum of T(d, a, b) over all child labels (a, b) of (h, k) in the semi-Baxter succession rule, with multiplicity given by the child indices.", DescribeRole.Definition),
            Node("weak-ascent-weakascentcounting-weakextensions", "Extensions with a prescribed prefix", "weakExtensions",
                "The extensions of a sequence e at depth d are the 210-avoiding weak ascent sequences of length equal to the length of e plus d whose prefix of length equal to the length of e is e.", DescribeRole.Definition),
            Node("weak-ascent-weakascentcounting-weak-extensions-count", "The extension count", "weak_extensions_count",
                "For every nonempty 210-avoiding weak ascent sequence e with label (h, k) and every nonnegative depth d, the number of extensions of e at depth d equals T(d, h, k).", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
