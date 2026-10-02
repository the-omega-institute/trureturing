using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackParallelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackParallel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For h at least one, P(h) is a simple permutation of the integers from one through 2h and belongs to both D and C.",
        H("Simplicity of the parallel family"),
        Blocks(
            Node("pop-stack-popstackparallel-p", "Two alternating decreasing chains", "P",
                "For each nonnegative h, P(h) has length 2h. At zero-based even position i its entry is h minus i/2, and at odd position i its entry is 2h minus floor(i/2). Thus the two decreasing value chains alternate.", DescribeRole.Definition),
            Node("pop-stack-popstackparallel-parallel-simple", "Simplicity of the parallel family", "parallel_simple",
                "For h at least one, P(h) is a simple permutation of the integers from one through 2h and belongs to both D and C.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
