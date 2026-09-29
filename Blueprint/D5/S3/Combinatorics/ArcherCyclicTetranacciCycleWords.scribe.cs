using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicTetranacciCycleWordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicTetranacciCycleWords.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rooted cycle word determines a permutation through its cyclic successors.",
        H("From Cycle Words to Permutations"),
        Blocks(
            Node("archer-cyclic-one-line", "Successor permutation", "oneLine",
                "The one-line permutation of a cycle word records the cyclic successor of each integer from one through the word length.", DescribeRole.Definition),
            Node("archer-cyclic-orbit-recovery", "Recovery of a rooted cycle word", "orbitWord_oneLine",
                "If a word begins with one and contains every integer from one through its length exactly once, the orbit word of its successor permutation is the original word.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
