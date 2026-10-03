using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicPadovanCycleWordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicPadovanCycleWords.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The orbit word of a cyclic permutation recovers its one-line form.",
        H("Recovering a Cyclic Permutation"),
        Blocks(Node("archer-cyclic-padovan-one-line-recovery", "Recover the one-line permutation", "oneLine_orbitWord",
            "For a cyclic permutation of the integers from one through its length, the successor permutation of its orbit word is the original permutation.",
            DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
