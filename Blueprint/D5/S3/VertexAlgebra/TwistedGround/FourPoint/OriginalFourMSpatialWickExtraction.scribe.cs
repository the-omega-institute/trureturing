using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSpatialWickExtractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spatial Taylor extraction through the Wick recursion",
        H("Ordered coefficients of analytic factors"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-extraction-dependson"),
                DeclarationHandle.Create(Prefix + "DependsOn"),
                H("Dependence on selected coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The function takes equal values at any two inputs that agree on the selected coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-extraction-spatialcoefficient-mul-filter"),
                DeclarationHandle.Create(Prefix + "spatialCoefficient_mul_filter"),
                H("Extraction on disjoint coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For factors supported on the true and false fibres of a Boolean predicate, the ordered "
                    + "Taylor coefficients on the corresponding filtered subwords multiply to the coefficient of "
                    + "the product at any evaluation point."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-extraction-partition-eq-filters"),
                DeclarationHandle.Create(Prefix + "partition_eq_filters"),
                H("Recovering the two ordered subwords"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a word of distinct labels and a position partition, filtering by membership in the "
                    + "first subword gives that subword. Filtering by its complement gives the second subword."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-extraction-spatialcoefficient-mul-partition"),
                DeclarationHandle.Create(Prefix + "spatialCoefficient_mul_partition"),
                H("Extraction on a position partition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When each factor depends only on its own subword of a distinct occurrence word, the "
                    + "ordered Taylor coefficient of the product factors along the partition at any evaluation "
                    + "point."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-extraction-wick-dependson"),
                DeclarationHandle.Create(Prefix + "wick_dependsOn"),
                H("Occurrence support of Wick evaluation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The spatial Wick evaluation depends on the coordinates in the occurrence word, because "
                    + "each singleton and pair in the recursion uses only those coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-extraction-spatialcoefficient-add"),
                DeclarationHandle.Create(Prefix + "spatialCoefficient_add"),
                H("Additivity on analytic germs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two germs analytic at zero, applying the ordered spatial coefficient at zero to their "
                    + "sum gives the sum of their coefficients."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-extraction-wick-analytic"),
                DeclarationHandle.Create(Prefix + "wick_analytic"),
                H("Analyticity of Wick evaluation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finitely many coordinates, analyticity at zero of the pair and singleton entries "
                    + "implies analyticity of the Wick evaluation for any occurrence word."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-extraction-spatialcoefficient-list-sum"),
                DeclarationHandle.Create(Prefix + "spatialCoefficient_list_sum"),
                H("Extraction through a finite list sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient at zero of a list sum of analytic germs equals the sum of their "
                    + "coefficients, counted with the multiplicities of the list."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-extraction-spatialcoefficient-wick"),
                DeclarationHandle.Create(Prefix + "spatialCoefficient_wick"),
                H("Extraction into the Wick entries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a distinct occurrence word and pair and singleton germs analytic at zero, the spatial "
                    + "coefficient of the Wick evaluation equals its Wick value with extracted entries. Take the "
                    + "singleton coefficient at its mode and each pair coefficient at both modes in occurrence "
                    + "order."))),
                DescribeRole.Theorem))));
}
