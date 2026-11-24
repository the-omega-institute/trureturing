using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Wick;

internal sealed class AffineWickAssignmentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickAssignments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wick transport by finite label assignments",
        H("Transport of an occurrence word"),
        Blocks(
            Describe.Lean(DescribeId.Create("affine-wick-assignments-assign"),
                DeclarationHandle.Create(Prefix + "assign"),
                H("Independent assignments"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every position of a word, sum over the finite native label type and multiply "
                    + "by the corresponding entry of the transport matrix. The empty word evaluates the function "
                    + "on the empty native word."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("affine-wick-assignments-wick-transport"),
                DeclarationHandle.Create(Prefix + "wick_transport"),
                H("Wick evaluation commutes with transport"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite native label type, transport matrix, complex covariance matrix, "
                    + "mean, and occurrence word, the Wick evaluation with the transported covariance and mean "
                    + "equals the weighted sum of the native Wick evaluations. Induction on word length "
                    + "separates the mean term from the covariance terms. Each covariance term sums the labels "
                    + "at its two paired positions and evaluates the remaining word with those positions erased."))),
                DescribeRole.Theorem))));
}
