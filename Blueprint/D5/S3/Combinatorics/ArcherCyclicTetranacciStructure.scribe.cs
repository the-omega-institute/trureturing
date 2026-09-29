using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicTetranacciStructureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicTetranacciStructure.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint cycle-form and one-line avoidance bounds the shape of the low arc.",
        H("Structure of Admissible Cycle Words"),
        Blocks(
            Node("archer-cyclic-first-high", "First high letter", "first_high_minimum",
                "When the high arc is a permutation of a consecutive interval, avoidance of 1324 in the cycle word and 4123 in its successor permutation forces the first high letter to be the smallest in that interval.", DescribeRole.Theorem),
            Node("archer-cyclic-low-length", "Length of the low arc", "low_arc_length_le_two",
                "If the high arc begins with its smallest possible letter and the successor permutation avoids 4123, the increasing low arc after two has length at most two.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
