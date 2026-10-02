using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscentSitesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscentSites.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/benyi2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Record positions determine how active insertion sites change after inserting a new maximum.",
        H("Active Sites and Records"),
        Blocks(
            Node("weak-ascent-weakascentsites-activesites", "Active insertion sites", "activeSites",
                "For a word p of length n, the active sites are the positions from zero through n at which inserting n + 1 gives a word avoiding 2-41-3.", DescribeRole.Definition),
            Node("weak-ascent-weakascentsites-recordsites", "Record positions", "recordSites",
                "The record positions of a word are the positions whose entries are strictly greater than every entry at an earlier position. Positions are numbered from zero.", DescribeRole.Definition),
            Node("weak-ascent-weakascentsites-active-record-structure", "Active sites up to the maximum", "active_record_structure",
                "In every nonempty permutation of one through n avoiding 2-41-3, the active sites at or before the position of n are exactly the record positions, every record position is at or before the position of n, and the two end sites zero and n are active.", DescribeRole.Theorem),
            Node("weak-ascent-weakascentsites-active-sites-insert", "Active sites after insertion", "active_sites_insert",
                "Let p be a permutation of one through n avoiding 2-41-3, and insert n + 1 at an active site s. The active sites of the resulting permutation are exactly the record positions of p strictly less than s, the sites s and s + 1, and the sites obtained by adding one to each active site of p strictly greater than s.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
