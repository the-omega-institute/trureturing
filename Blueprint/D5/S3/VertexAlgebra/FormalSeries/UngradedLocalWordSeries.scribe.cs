using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class UngradedLocalWordSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed coefficient readout", H("Signed coefficient readout"), Blocks(
            Describe.Lean(DescribeId.Create("ungradedlocalwordseries-polynomialaction-map"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries.polynomialAction_map"),
                H("polynomialAction_map"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite Laurent convolution commutes with a complex-linear readout."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ungradedlocalwordseries-signedextend-map"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries.signedExtend_map"),
                H("signedExtend_map"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Signed zero extension commutes with complex-linear maps."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ungradedlocalwordseries-ungraded-local-word-common-series"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries.ungraded_local_word_common_series"),
                H("ungraded_local_word_common_series"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite complete word of mutually local fields has one generally infinite vector series after pair clearing and statewise monomial shifting. Its locality order is chosen before the input vector. The existing weighted-locality theorem supplies permutation equality and coordinate lower support."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-index"),
                DeclarationHandle.Create(Prefix + "signedIndex"),
                H("signedIndex"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Convert each nonnegative signed exponent to a native finitely supported multi-index. This index imposes no finite support on a series."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("signed-extend"),
                DeclarationHandle.Create(Prefix + "signedExtend"),
                H("signedExtend"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Extend the native coefficient function by zero whenever any signed exponent is negative."))), DescribeRole.Definition))));
}
