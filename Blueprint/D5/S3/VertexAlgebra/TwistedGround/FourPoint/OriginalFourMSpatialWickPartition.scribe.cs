using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSpatialWickPartitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-charge spatial Wick factors in the physical charts",
        H("Native entries and inverse-coordinate corrections"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-partition-liftedscale"),
                DeclarationHandle.Create(Prefix + "liftedScale"),
                H("Signed inverse scale"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each occurrence contributes the relative chart sign, the inverse chosen root, and the "
                    + "inverse chart scale to the power of its requested mode."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-partition-correction-pair-coefficient"),
                DeclarationHandle.Create(Prefix + "correction_pair_coefficient"),
                H("Physical correction and the oscillator pair polynomial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any chart, puncture and two oscillator indices at an interior real argument, the "
                    + "signed two-variable Taylor coefficient of the physical slot correction divided by its two "
                    + "Jacobians is the evaluated central pair polynomial times the two signed inverse scales. "
                    + "The evaluation uses the negative lowering parameter and takes the constant oscillator "
                    + "coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-partition-nativetaylor"),
                DeclarationHandle.Create(Prefix + "nativeTaylor"),
                H("Native spatial entries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take both ordinary Taylor coefficients of the signed native chart covariance after "
                    + "coordinate substitution and division by the two Jacobians."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-partition-correctiontaylor"),
                DeclarationHandle.Create(Prefix + "correctionTaylor"),
                H("Same-puncture spatial entries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Within one puncture the correction entry is the evaluated oscillator pair polynomial times "
                    + "both signed scales. Across distinct punctures it is zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-four-mspatial-wick-partition-physical-marked-coefficient-wick-partition"),
                DeclarationHandle.Create(Prefix + "physical_marked_coefficient_wick_partition"),
                H("Exact physical marked coefficient at fixed charge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any fixed charge, chart and chart flag, an interior argument and a word of distinct "
                    + "marks with prescribed punctures, colours and modes, take first degree in the chosen mark "
                    + "variables and the prescribed degrees in the spatial variables. The coefficient equals the "
                    + "charge exponential times the finite sum over ordered position partitions. Evaluate the "
                    + "first subword with the same-puncture correction matrix and zero mean. Evaluate the second "
                    + "subword with the native Taylor covariance and the extracted signed charge-linear means."))),
                DescribeRole.Theorem))));
}
