using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicTetranacciDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicTetranacciDecomposition.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The admissible rooted cycle words decompose into four insertion branches.",
        H("Four-Branch Decomposition"),
        Blocks(
            Node("archer-cyclic-tetranacci-words", "Admissible rooted words", "words",
                "These words list the integers from one through n, begin with one, avoid 1324 in every rotation, and have successor permutations avoiding 4123.", DescribeRole.Definition),
            Node("archer-cyclic-tetranacci-decomposition", "Insertion decomposition", "decomposition",
                "For n greater than one, a word is admissible exactly when it is obtained by inserting a low arc of length one, two, three, or four into an admissible shorter word.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
