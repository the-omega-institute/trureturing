using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215TransitionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215Transitions.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Appending a letter induces record, fresh-site or old-site transitions on the active marks.",
        H("Transitions of Active Marks"),
        Blocks(
            Node("weak-ascent-weakascent215transitions-left-transitions", "The active-mark transition correspondence", "left_transitions",
                "For a nonempty word w in the class avoiding 100, 101, 110 and 201, put M equal to its maximum, b equal to one plus its weak ascent count minus M, and e true exactly when its last entry is M. Appendable letters are in bijection with either a gap g below b or a position s in the increasing active-value list. The gap choice appends M + g + 1, appends g false marks and a true mark, changes the budget to b minus g and sets true mode. A site choice appends its active value. At a false mark it truncates the mark list before s, retains budget b and sets false mode. At a true mark with e true and s last, it leaves the singleton true list, changes the budget to b + 1 and sets true mode. At any other true mark it leaves the empty list, retains budget b and sets false mode.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
