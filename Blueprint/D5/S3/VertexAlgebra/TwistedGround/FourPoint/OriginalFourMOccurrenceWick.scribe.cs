using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMOccurrenceWickDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Correction partitions for the physical four-point coefficient",
        H("Fixed-charge marking and charge summation"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-four-moccurrence-wick-correction-entry"),
                DeclarationHandle.Create(Prefix + "correctionEntry"),
                H("Signed correction covariance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each entry is the negative inverse-coordinate correction divided by the two "
                    + "half-Jacobians and weighted by the Gram entry and both relative signs. Corrections "
                    + "between different punctures vanish."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-four-moccurrence-wick-native-entry"),
                DeclarationHandle.Create(Prefix + "nativeEntry"),
                H("Signed native covariance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each entry is the chart covariance evaluated in the two raw local coordinates, "
                    + "divided by both half-Jacobians and weighted by the Gram entry and both relative "
                    + "signs."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-four-moccurrence-wick-physical-mark-jet-partition"),
                DeclarationHandle.Create(Prefix + "physical_mark_jet_partition"),
                H("Partition of the fixed-charge mark derivative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ordered mark derivative of the physical summand equals its charge-energy "
                    + "exponential times a position partition sum. The correction covariance supplies the "
                    + "first subword with zero mean. The pulled-back chart covariance and the physical mean "
                    + "supply the second subword. Symmetry of the two covariances permits the Wick "
                    + "convolution."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-moccurrence-wick-physical-marked-coefficient-partition"),
                DeclarationHandle.Create(Prefix + "physical_marked_coefficient_partition"),
                H("Partition of the literal physical marked coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a word of distinct mark labels, extract degree one in each selected weight and "
                    + "the prescribed spatial degree at each mark. The result is the fixed-charge "
                    + "exponential times the same spatial extraction of the correction and native Wick "
                    + "partition sum. Distinct mark labels can have equal colours or punctures."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-moccurrence-wick-physical-marked-partition-has-sum"),
                DeclarationHandle.Create(Prefix + "physical_marked_partition_hasSum"),
                H("Charge-fiber sum of partitioned coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a word of distinct mark labels, assume a unit Gram determinant, a positive "
                    + "definite real Gram form and 0 < x < 1. Sum the partitioned coefficients over "
                    + "charges reducing to the given mod-two sector. The "
                    + "inverse twelfth power of the chart period weights each term. The sum is the literal "
                    + "marked coefficient of the physical four-point product."))),
                DescribeRole.Theorem))));
}
