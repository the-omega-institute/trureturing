using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class CircuitDifferenceBasisDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral difference coordinates with a representative inside a block.",
        H("Difference Coordinates around Two Representatives"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-difference-basis"),
                DeclarationHandle.Create(Module + ".exists_difference_basis"),
                H("Difference vectors in a block and its complement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose a global representative outside the block and a local representative "
                    + "inside. A vector at another index in the block becomes its difference from "
                    + "the local representative. Every other non-global index uses its difference "
                    + "from the global representative. The two corresponding coordinates of a "
                    + "vector are its block sum and its total sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-two-face-difference-basis"),
                DeclarationHandle.Create(Module + ".exists_two_face_difference_basis"),
                H("Simultaneous coordinates for the two face differences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When both faces have a common vertex, choose it as their representative. For disjoint faces, "
                    + "choose separate representatives and sum the weights in the second face into its representative's "
                    + "coordinate. In either case the difference tuples occur together in an integral basis, the "
                    + "transformed weights stay positive, and the first tuple has at least two indices outside the second."))),
                DescribeRole.Theorem))));
}
