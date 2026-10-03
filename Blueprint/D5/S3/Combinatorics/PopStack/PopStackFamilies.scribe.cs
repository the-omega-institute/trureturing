using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackFamiliesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackFamilies.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For n at least two, A(n) does not end in its minimum and B(n) does. A permutation of size n belongs to D and has every proper nontrivial interval starting at its first position if and only if it equals A(n) or B(n).",
        H("Classification when all intervals are prefixes"),
        Blocks(
            Node("pop-stack-popstackfamilies-a", "The nonterminal prefix family", "A",
                "For even n, A(n) equals P(n/2). For odd n, A(n) is obtained by inflating the first entry of P(floor(n/2)) by 21.", DescribeRole.Definition),
            Node("pop-stack-popstackfamilies-b", "The terminal prefix family", "B",
                "Set B(2) = 21. At every other size n, B(n) is obtained by adding one to every entry of A(n-1) and appending one. Subtraction of nonnegative integers is truncated at zero.", DescribeRole.Definition),
            Node("pop-stack-popstackfamilies-prefix-families", "Classification when all intervals are prefixes", "prefix_families",
                "For n at least two, A(n) does not end in its minimum and B(n) does. A permutation of size n belongs to D and has every proper nontrivial interval starting at its first position if and only if it equals A(n) or B(n).", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
