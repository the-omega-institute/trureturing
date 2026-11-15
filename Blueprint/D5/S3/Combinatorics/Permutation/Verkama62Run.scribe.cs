using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class Verkama62RunDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/Verkama62Run.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/verkama2026connectivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deletion connectivity of northeast ear runs.", H("Deletion connectivity of northeast ear runs"), Blocks(
            Node("verkama62-run-earrun-robust", "Deletion connectivity", "robust",
                "For every permutation pi, finite set S, and permitted ear run on S, deleting any ambient point w leaves the induced value graph on pi(S minus {w}) connected. A triangle and a 3412 square have this property. Inserting a singleton with at least two old neighbours leaves an attachment after any deletion. A double ear has distinct old attachments and an edge between its two new vertices; after any one deletion its surviving new vertices connect to the surviving old stage.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
