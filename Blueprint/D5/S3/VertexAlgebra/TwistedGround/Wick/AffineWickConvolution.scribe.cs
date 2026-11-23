using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Wick;

internal sealed class AffineWickConvolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickConvolution.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wick expansion for a sum of covariances",
        H("Partitioning an occurrence word"),
        Blocks(
            Describe.Lean(DescribeId.Create("affine-wick-convolution-partitions"),
                DeclarationHandle.Create(Prefix + "partitions"),
                H("Ordered partitions by position"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose one of two subwords for each position. Both subwords retain the order in the "
                    + "input word, and the list of partitions retains multiplicities."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("affine-wick-convolution-wick-add-covariance"),
                DeclarationHandle.Create(Prefix + "wick_add_covariance"),
                H("Convolution of Wick evaluations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two symmetric covariances on a finite type, the Wick evaluation with their sum "
                    + "equals the sum over position partitions. Evaluate the first subword using the "
                    + "correction covariance and zero mean. Evaluate the second with the original covariance "
                    + "and mean. The product rule for the ordered derivatives of the factorized affine "
                    + "Gaussian gives the partition sum."))),
                DescribeRole.Theorem))));
}
