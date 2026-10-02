using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscentInsertionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscentInsertion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/benyi2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Insertion and deletion of a largest letter characterize avoidance of 2-41-3.",
        H("Inserting a New Maximum"),
        Blocks(
            Node("weak-ascent-weakascentinsertion-delete-maximum-avoids", "Deletion of the inserted maximum", "delete_maximum_avoids",
                "Let a new letter exceed every entry of a word p, and insert it at any position from zero through the length of p. If the resulting word avoids 2-41-3, then p also avoids 2-41-3.", DescribeRole.Theorem),
            Node("weak-ascent-weakascentinsertion-active-site-criterion", "The insertion criterion", "active_site_criterion",
                "Let p avoid 2-41-3, let s be a position from zero through its length, and let a new letter exceed every entry of p. Inserting this letter at s preserves avoidance exactly when there are no positions i and k with i less than s less than k less than the length of p such that the entry at s is less than the entry at i and the entry at i is less than the entry at k. Positions are numbered from zero.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
