using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackPrefixShapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackPrefixShape.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let p be a permutation of size n at least three in D whose proper nontrivial intervals are all prefixes and whose final entry is not the minimum. For some h at least one, either n = 2h and p = P(h), or n = 2h + 1 and p is the first-entry inflation of P(h) by 21.",
        H("A nonterminal prefix-only permutation"),
        Blocks(
            Node("pop-stack-popstackprefixshape-prefix-nonterminal", "A nonterminal prefix-only permutation", "prefix_nonterminal",
                "Let p be a permutation of size n at least three in D whose proper nontrivial intervals are all prefixes and whose final entry is not the minimum. For some h at least one, either n = 2h and p = P(h), or n = 2h + 1 and p is the first-entry inflation of P(h) by 21.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
