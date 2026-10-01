using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic pattern avoiders and the two counting sequences are defined.",
        H("Cyclic Pattern Avoidance"),
        Blocks(
            Node("archer-cyclic-image", "Image of a permutation", "image",
                "The image of x is the list entry at zero-based index x minus one, with zero used when that index is beyond the list.", DescribeRole.Definition),
            Node("archer-cyclic-orbit-word", "Orbit word", "orbitWord",
                "The orbit word lists the first n iterates of one under a permutation of length n.", DescribeRole.Definition),
            Node("archer-cyclic-is-cyclic", "Single-cycle condition", "IsCyclic",
                "A permutation is cyclic when its orbit word contains each integer from one through its length exactly once.", DescribeRole.Definition),
            Node("archer-cyclic-avoiders", "Cyclic avoiders", "cyclicAvoiders",
                "This set consists of cyclic permutations of n letters whose one-line form avoids the first pattern and whose every rotated cycle word avoids the second pattern.", DescribeRole.Definition),
            Node("archer-cyclic-tetranacci-sequence", "Tetranacci sequence", "tetranacci",
                "The sequence begins 0, 0, 0, 1, and each later term is the sum of the previous four terms.", DescribeRole.Definition),
            Node("archer-cyclic-padovan-sequence", "Padovan sequence", "padovan",
                "The sequence begins 1, 0, 0, and each term from index three onward is the sum of the terms two and three positions earlier.", DescribeRole.Definition),
            Node("archer-cyclic-tetranacci-claim", "Tetranacci count", "tetranacciClaim",
                "For every positive n, the number of cyclic permutations avoiding 4123 in one-line form and 1324 in every cycle form equals the Tetranacci number at index n plus two.", DescribeRole.Definition),
            Node("archer-cyclic-padovan-claim", "Padovan count", "padovanClaim",
                "For every positive n, the number of cyclic permutations avoiding 4132 in one-line form and 1324 in every cycle form equals the Padovan number at index three times n.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
