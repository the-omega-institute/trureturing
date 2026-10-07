using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class TripleAvoidingMatchingsBulkDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsBulk.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The height-two suffix series is expressed by Catalan shapes and Fibonacci phase weights.",
        H("Catalan-Fibonacci enumeration above the boundary"),
        Blocks(
            Node("bss-bulk-bulk-enumeration", "The Catalan-Fibonacci continuation formula", "bulk_enumeration",
                "With x counting scan actions, the normal-phase suffix series at height two equals xH(x^2) times the normal-phase suffix series at height one. The transition matrix D = ((1,1),(1,0)) retains both phases above height two. Its kth power weights the Cat_k excursion shapes, and the exit vector (2,1) gives the Fibonacci factor F_{k+3}.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
