using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicPadovanSuccessorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The successor permutation of a split cycle word has an explicit block form.",
        H("Successors of Padovan Cycle Words"),
        Blocks(
            Node("archer-cyclic-padovan-split-line", "Successors of a split word", "oneLine_split_block",
                "For a distinct-letter word beginning with one, followed by a high block, two, and the consecutive low block starting at three, its successor permutation begins with the first high letter and the low block, then one, followed by the successors of the remaining high letters.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-raise-successor", "Relabel a successor", "raiseSuccessor",
                "This map sends one to two, fixes zero, and raises every value at least two by m minus one.", DescribeRole.Definition),
            Node("archer-cyclic-padovan-descent-map", "Descending pair under relabeling", "below_descent_map_iff",
                "A strictly increasing relabeling preserves whether a word has a descending pair whose larger entry lies below a specified threshold.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-insert-line", "Successors after block insertion", "oneLine_inserted_block",
                "Inserting a consecutive low block after a raised high block gives a successor permutation consisting of the raised first high letter, the low successors, one, and the relabeled tail of the old successor permutation.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-insert-avoid-iff", "4132 avoidance after insertion", "inserted_avoid_iff",
                "The inserted successor permutation avoids 4132 exactly when the old successor tail avoids 4132 and contains no descent whose larger entry lies below the first high letter.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
