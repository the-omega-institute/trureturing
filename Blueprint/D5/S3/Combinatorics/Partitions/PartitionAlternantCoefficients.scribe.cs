using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class PartitionAlternantCoefficientsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026partitionalternants");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shifted row lengths distinguish the literal partition labels in finite-variable alternants.",
        H("Coefficients of partition alternants"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partition-alternant-coefficient"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/PartitionAlternantCoefficients.partition_alternant_coefficient"),
                H("The coefficient for an original partition label"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The parameters are an arbitrary commutative coefficient ring, an arbitrary degree, an independent finite row bound, and two partitions of that degree. Both Young diagrams have at most the specified number of rows. The determinant uses their actual row lengths, padded by zeros, shifted by the descending staircase. Its coefficient is one for the same partition and zero for every different partition.")),
                    Paragraph(Text("Expand the determinant using the selected upstream signed-permutation coefficient formula. On the diagonal, injectivity of the beta-numbers leaves precisely the identity permutation. Off the diagonal, a contributing permutation would identify the multisets of the two strictly decreasing beta-number lists. Uniqueness of a sorted list makes the lists equal. The selected upstream reconstruction of a diagram from its beta-numbers, followed by injectivity of Mathlib's original partition-to-diagram map, then contradicts distinctness of the partitions."))),
                DescribeRole.Theorem),
            Paragraph(Text("For three variables the descending staircase is the triple two, one, zero. Zero row lengths remain in scope, so the intended application includes one-row and two-row shapes and the rectangle with final coordinate zero. The alphabet bound does not bound the degree.")),
            Paragraph(Text("This coefficient-isolation source is one step in the comparison with ordinary Specht characters. It contains no hypothesis asserting that comparison. Completing it requires the arbitrary-alphabet power-sum expansion in Schur polynomials, the division-free bialternant identity, vanishing of Schur polynomials with too many rows, and the character identity for the complex scalar extension of the rational polytabloid Specht module of the same partition. The full permutation partition must retain fixed-point parts equal to one.")),
            Paragraph(Text("The Hemmer–Straub–Westrem target still ranges over every positive degree, every partition, every positive Ev cycle list with its multiplicities, every even shape with at most three rows, and the rectangle. The supplied reciprocal-centralizer weighted argument, its signed left sum, both equalities and its even-binomial or odd-zero value are separate existing mathematics. They are not reproduced here.")),
            Paragraph(Text("This is source preparation. Native Lean checking at the unchanged repository pins, current source-bound reports, rendered statement comparison, escape registration, freezing and required CI remain pending. No equality with an ordinary trace is claimed by this unit.")))));
}
