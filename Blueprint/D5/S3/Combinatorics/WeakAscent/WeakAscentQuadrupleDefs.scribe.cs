using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscentQuadrupleDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscentQuadrupleDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two quadruples of length-three patterns define the weak ascent sequence classes of Class 215.",
        H("Weak Ascent Sequences Avoiding Four Patterns"),
        Blocks(
            Node("weak-ascent-weakascentquadrupledefs-avoiders", "Avoiders of a pattern family", "avoiders",
                "For a nonnegative integer n and a list B of patterns, the avoiders are the weak ascent sequences of length n containing no pattern in B. Containment preserves both equalities and strict relative order among the selected entries.", DescribeRole.Definition),
            Node("weak-ascent-weakascentquadrupledefs-claim215", "The Class 215 equinumerosity assertion", "claim215",
                "For every nonnegative integer n, the number of weak ascent sequences of length n avoiding 100, 101, 110 and 201 equals the number avoiding 021, 101, 201 and 210. The same patterns written with letters starting at one are respectively 211, 212, 221, 312 and 132, 212, 312, 321.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
