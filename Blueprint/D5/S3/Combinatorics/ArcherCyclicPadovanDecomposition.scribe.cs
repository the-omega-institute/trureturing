using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicPadovanDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circular avoidance determines the lower arc and supports recovery of the rooted word.",
        H("Decomposing Padovan Cycle Words"),
        Blocks(
            Node("archer-cyclic-padovan-low-arc-forced", "Forced lower arc", "low_arc_forced",
                "If a rooted permutation word has a nonempty block before two and avoids 1324 in every rotation, all letters after two lie below that block, form the consecutive interval beginning at three, and the word formed by one and the first block also avoids 1324 circularly.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-recover-high", "Recover the high word", "recover_high_word",
                "A circularly 1324-avoiding rooted permutation word with a nonempty block before two is obtained by raising the letters of a shorter circularly avoiding rooted word and appending the consecutive low block.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-low-sufficient", "Sufficient lower-arc conditions", "low_arc_sufficient",
                "A distinct-letter word formed from one, a high block above two, two, and a consecutive lower block avoids 1324 in every rotation when the high block lies above the lower block and the word formed by one and the high block avoids 1324 circularly.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-insert-two", "Insert two at the front", "circular_avoidance_insert_two",
                "For a distinct-letter word whose letters after one exceed two, placing two immediately after one preserves circular avoidance of 1324 in both directions.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-insert-avoid", "Avoidance after high insertion", "inserted_word_circular_avoid",
                "Raising the letters of a rooted permutation word and appending two followed by a consecutive low block preserves circular avoidance of 1324.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-recover-front", "Recover the front-insertion word", "recover_front_word",
                "A circularly 1324-avoiding rooted permutation word beginning with one and two comes from front insertion into a shorter circularly avoiding rooted permutation word.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
