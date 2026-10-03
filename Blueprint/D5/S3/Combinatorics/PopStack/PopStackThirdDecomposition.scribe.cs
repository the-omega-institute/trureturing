using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackThirdDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackThirdDecomposition.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let p be a permutation of size at least five with minimum third, and form q by deleting that minimum and subtracting one from every remaining value. The permutation p is simple and in C if and only if q is a permutation in C reconstructing p by minimum insertion, and at least one of five cases holds: q is simple with minimum at zero-based position at least three; q is the second-entry inflation by 21 of a unique simple skeleton in C of size at least four whose minimum is not second; p is obtained by prepending two to a unique simple parent in C with minimum second while increasing its values other than one; p is obtained in the same way after second-entry inflation by 12 of a unique simple skeleton in C of size at least four with minimum second; or q belongs to D, ends in its minimum, and equals R at its size.",
        H("The five cases for a third-position minimum"),
        Blocks(
            Node("pop-stack-popstackthirddecomposition-minimum-three-decomposition", "The five cases for a third-position minimum", "minimum_three_decomposition",
                "Let p be a permutation of size at least five with minimum third, and form q by deleting that minimum and subtracting one from every remaining value. The permutation p is simple and in C if and only if q is a permutation in C reconstructing p by minimum insertion, and at least one of five cases holds: q is simple with minimum at zero-based position at least three; q is the second-entry inflation by 21 of a unique simple skeleton in C of size at least four whose minimum is not second; p is obtained by prepending two to a unique simple parent in C with minimum second while increasing its values other than one; p is obtained in the same way after second-entry inflation by 12 of a unique simple skeleton in C of size at least four with minimum second; or q belongs to D, ends in its minimum, and equals R at its size.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
