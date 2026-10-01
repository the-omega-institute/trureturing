using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackExtraDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackExtra.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For h at least one, E(h) is a permutation of size 2h + 1 in C and is not simple. Its only proper nontrivial interval is its prefix of length 2h, whose values are the integers from two through 2h + 1.",
        H("The unique proper interval of an odd extra"),
        Blocks(
            Node("pop-stack-popstackextra-e", "The odd extra family", "E",
                "For each nonnegative h, E(h) is obtained by adding one to every entry of P(h) and appending the minimum one.", DescribeRole.Definition),
            Node("pop-stack-popstackextra-odd-extra", "The unique proper interval of an odd extra", "odd_extra",
                "For h at least one, E(h) is a permutation of size 2h + 1 in C and is not simple. Its only proper nontrivial interval is its prefix of length 2h, whose values are the integers from two through 2h + 1.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
