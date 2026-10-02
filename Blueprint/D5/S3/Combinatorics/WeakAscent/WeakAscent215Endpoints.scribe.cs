using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeakAscent;

internal sealed class WeakAscent215EndpointsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeakAscent/WeakAscent215Endpoints.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/callan2025ascent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Terminal records and old entries describe the endpoints of pure histories.",
        H("Endpoints of Pure Histories"),
        Blocks(
            Node("weak-ascent-weakascent215endpoints-oldcount", "Old entries in the terminal stack", "oldCount",
                "The old-entry count of a pure history is the number of true marks in a terminal stack obtained by running that history from the empty stack.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215endpoints-finalpiece", "The final pure piece", "finalPiece",
                "The final piece of a recursive collection of original pieces is its terminal pure history, obtained by following the successive cuts to the final case.", DescribeRole.Definition),
            Node("weak-ascent-weakascent215endpoints-record-endings", "Histories ending in a record", "record_endings",
                "Pure histories whose last step is a record are in bijection with pairs consisting of a pure history and a nonnegative gap. Reconstruction appends a record of that gap, increasing the length by one and the expenditure by the gap.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
