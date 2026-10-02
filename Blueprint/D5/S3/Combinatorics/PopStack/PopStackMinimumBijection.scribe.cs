using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackMinimumBijectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackMinimumBijection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For n at least four, T(n) bijects augmented(n-1) with the simple permutations of size n in C having their minimum second. The map undoT(n) is its inverse on both sets.",
        H("A bijection to second-position minima"),
        Blocks(
            Node("pop-stack-popstackminimumbijection-t", "The recursive second-position construction", "T",
                "The map T(n,p) is empty at n = 0. At positive n, if p is simple and its minimum is not second, increase its entries and insert one second. If p is simple with minimum second, let r = undoT(n-1,p): when r is simple, first inflate its first entry by 21, and otherwise use B(n-1), then increase the entries and insert one second. For non-simple p, increase the entries of B(n-1) and insert one second.", DescribeRole.Definition),
            Node("pop-stack-popstackminimumbijection-undot", "The reverse second-position construction", "undoT",
                "The map undoT(n,p) is empty at n = 0. Otherwise delete the second entry and subtract one from the remaining values to obtain q. If q is simple, return q. If q = B(n-1), return E(floor((n-1)/2)) when n is even and T(n-1,E(floor((n-2)/2))) when n is odd. In the remaining case return T(n-1,deflateFirst(q)).", DescribeRole.Definition),
            Node("pop-stack-popstackminimumbijection-minimum-two-bijection", "A bijection to second-position minima", "minimum_two_bijection",
                "For n at least four, T(n) bijects augmented(n-1) with the simple permutations of size n in C having their minimum second. The map undoT(n) is its inverse on both sets.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
