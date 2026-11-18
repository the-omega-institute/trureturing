using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalFrequencyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frequency Vectors of the Original Signed Columns",
        H("Frequency Vectors of the Original Signed Columns"),
        Blocks(
            Paragraph(Text("The finite binomial contiguous identity realizes internal frequency multiplication as an actual Hilbert vector. The predecessor at positive mode zero is the negative zero label; no boundary is discarded.")),
            Describe.Lean(
                DescribeId.Create("externalparameter"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.externalParameter"),
                H("externalParameter"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameter is p+1/2 for true and -p-1/2 for false, for each natural p."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("predecessor"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.predecessor"),
                H("predecessor"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The predecessor lowers the parameter by one: positive zero goes to negative zero, positive successor to the previous positive mode, and negative p to negative p+1."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frequencyvector"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.frequencyVector"),
                H("frequencyVector"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The vector is alpha times the difference of the original external vector and its actual predecessor."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binomial-frequency"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.binomial_frequency"),
                H("binomial_frequency"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For both signed labels and all natural p,s, s times the actual external binomial equals alpha times its contiguous predecessor difference."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("frequencyvector-apply"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.frequencyVector_apply"),
                H("frequencyVector_apply"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Throughout the complex unit disk, every coordinate of the actual frequencyVector is n+1 times the original externalColumn at n."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("externalvector-negative-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequency.externalVector_negative_zero"),
                H("externalVector_negative_zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Throughout the complex unit disk, the actual negative external zero vector is exactly minus sourceFamily 1."))), DescribeRole.Theorem))));
}
