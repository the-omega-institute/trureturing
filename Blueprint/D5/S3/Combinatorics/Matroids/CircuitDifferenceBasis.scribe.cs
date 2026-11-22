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
                DescribeRole.Theorem))));
}
