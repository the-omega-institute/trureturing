using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.VincularStack;

internal sealed class VincularStackThreeDivergenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/VincularStack/VincularStackThreeDivergence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/zhao2024vincular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A push permitted by the stack avoiding 3-12 but forbidden by the stack avoiding 312 forces a 231 occurrence.",
        H("Different Push Decisions Force 231"),
        Blocks(
            Node("vincularstack-vincularstackthreedivergence-divergence", "The structure of different push decisions", "divergence",
                "Suppose an entry followed by a stack has distinct entries, the stack avoids classical 312, and pushing the entry creates classical 312 but not 3-12 with the entries playing 1 and 2 adjacent. Then the stack is a nonempty prefix followed by a high entry and a tail containing a low entry. Every entry of the prefix is less than the low entry, which is less than the inserted entry, which is less than the high entry. Insertion avoiding 312 pops exactly that prefix and leaves the inserted entry followed by the high entry and the tail; insertion avoiding 3-12 pops nothing and leaves the inserted entry followed by the original stack. Both resulting stacks contain classical 231.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
