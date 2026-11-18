using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class Verkama62CountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/Verkama62Count.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/verkama2026connectivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact inversion increments.",
        H("Exact inversion increments"),
        Blocks(
            Node("verkama62-count-inversions", "Increasing-position pair count", "inversions",
                "For pi and S, sum over ordered pairs i,j in S the indicator of i < j and pi(j) < pi(i). Each unordered inversion edge contributes exactly once.", DescribeRole.Definition),
            Node("verkama62-count-inversions-insert", "Singleton increment", "inversions_insert",
                "For x outside S, the inversion count of S union {x} equals the old inversion count plus the number of old inversion neighbours of x. The two possible orientations partition those neighbours.", DescribeRole.Theorem),
            Node("verkama62-count-double-inversion-increment", "Double-ear increment", "inversion_increment",
                "A northeast double ear adds exactly three inversions: v has the unique old neighbour y, and u has neighbours x and v when added second. The total increment is three, independent of the size of S.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
