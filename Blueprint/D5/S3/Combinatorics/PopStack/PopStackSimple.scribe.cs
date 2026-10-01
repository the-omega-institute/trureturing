using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackSimpleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackSimple.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The numbers of simple permutations in C of sizes zero, one and two are respectively one, one and two. For every n at least three, the number of simple permutations of size n sortable by two parallel pop stacks with bypass is F_(2n-5) minus the remainder of n on division by two, where F_0 = 0 and F_1 = 1.",
        H("The Fibonacci enumeration"),
        Blocks(
            Node("pop-stack-popstacksimple-result", "The Fibonacci enumeration", "result",
                "The numbers of simple permutations in C of sizes zero, one and two are respectively one, one and two. For every n at least three, the number of simple permutations of size n sortable by two parallel pop stacks with bypass is F_(2n-5) minus the remainder of n on division by two, where F_0 = 0 and F_1 = 1.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
