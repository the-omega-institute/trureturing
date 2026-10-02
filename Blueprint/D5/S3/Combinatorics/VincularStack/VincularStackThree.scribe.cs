using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.VincularStack;

internal sealed class VincularStackThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/VincularStack/VincularStackThree.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/zhao2024vincular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stacks avoiding 312, 31-2 and 3-12 sort the same permutations and agree on their outputs.",
        H("Equal Sorting Classes and Outputs"),
        Blocks(
            Node("vincularstack-vincularstackthree-result", "Equal sorting classes and outputs", "result", "For every positive n, the sorting classes of the stacks avoiding 312, 31-2 with the entries playing 3 and 1 adjacent, and 3-12 with the entries playing 1 and 2 adjacent are equal. On every permutation in the common sorting class, the three stack maps have equal outputs.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
