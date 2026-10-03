using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicPadovanRotationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicPadovanRotation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pattern occurrences in circular subwords can be transferred between rotations.",
        H("Rotations and Circular Subwords"),
        Blocks(
            Node("archer-cyclic-padovan-rotate-sublist", "Rotate a subword", "rotate_sublist_of_sublist",
                "Every rotation of a subsequence of a word is a subsequence of some rotation of the full word.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-rotate-first", "Root a circular quadruple", "rotate_quadruple_to_first",
                "If four letters occur in order in some rotation, another rotation begins with the first of those letters and has the other three as a subsequence of its tail.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-subword-avoid", "Circular avoidance of subwords", "circular_avoidance_sublist",
                "Every subsequence of a word that avoids a fixed pattern in all rotations also avoids that pattern in all of its own rotations.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-minimum-rooted", "Root a 1324 occurrence", "circular_1324_iff_minimum_rooted",
                "A circular word contains 1324 in some rotation exactly when some rotation begins with a letter a and has a subsequence c, b, d in its tail with a less than b less than c less than d.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
