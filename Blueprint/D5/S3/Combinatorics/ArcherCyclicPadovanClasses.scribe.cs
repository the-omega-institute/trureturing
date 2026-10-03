using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicPadovanClassesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicPadovanClasses.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two classes of rooted cycle words organize the Padovan enumeration.",
        H("Rooted Cycle-Word Classes"),
        Blocks(
            Node("archer-cyclic-padovan-circle-words", "Circularly avoiding words", "circleWords",
                "These are permutations of the integers from one through n that begin with one and avoid 1324 in every rotation.", DescribeRole.Definition),
            Node("archer-cyclic-padovan-good-words", "Good words", "goodWords",
                "A good word is a circularly 1324-avoiding rooted word whose successor permutation also avoids 4132.", DescribeRole.Definition),
            Node("archer-cyclic-padovan-tail-condition", "Tail condition", "tailCondition",
                "The tail of the successor permutation avoids 4132 and contains no descent whose larger entry lies below the first letter of the cycle word's tail, with zero used when that tail is empty.", DescribeRole.Definition),
            Node("archer-cyclic-padovan-aux-words", "Auxiliary words", "auxWords",
                "An auxiliary word of index k is a circularly 1324-avoiding rooted word of length k plus one satisfying the tail condition.", DescribeRole.Definition),
            Node("archer-cyclic-padovan-aux-arc", "End of an auxiliary arc", "auxiliary_arc_ends_at_two",
                "For a distinct-letter word of the form one, h, T, two, R, where R is consecutive from three and all its letters lie below h, the tail condition forces R to be empty.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-aux-shape", "Shape of an auxiliary word", "auxiliary_word_shape",
                "Every auxiliary word of positive index either begins with one and two or begins with one, has a nonempty middle block, and ends with two.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-last-tail", "Tail condition after final insertion", "auxiliary_last_insert_iff",
                "For a rooted permutation word with a nonempty tail, raising its tail letters and appending two preserves the tail condition in both directions.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-front-good", "Good words under front insertion", "front_insert_good_iff",
                "Inserting a new low letter at the front carries a rooted permutation word into the good class exactly when the original word is good.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-high-good", "Good words under high insertion", "high_insert_good_iff",
                "For a rooted permutation word and a low block of length at least two, high-block insertion produces a good word exactly when the original word is auxiliary.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-front-aux", "Auxiliary words under front insertion", "front_insert_aux_iff",
                "Front insertion produces an auxiliary word exactly when the original rooted permutation word is good.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-last-aux", "Auxiliary words under final insertion", "last_insert_aux_iff",
                "Raising the tail letters and appending two produces an auxiliary word exactly when the original rooted permutation word is auxiliary.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
