using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackThirdEquivalenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackThirdEquivalence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n at least four, Phi(n) bijects the simple permutations of size n in C with minimum second and those with minimum third. The map undoPhi(n) is its inverse on both sets.",
        H("Second-position and third-position minima"),
        Blocks(
            Node("pop-stack-popstackthirdequivalence-third-minimum-bijection", "Second-position and third-position minima", "third_minimum_bijection",
                "For every n at least four, Phi(n) bijects the simple permutations of size n in C with minimum second and those with minimum third. The map undoPhi(n) is its inverse on both sets.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
