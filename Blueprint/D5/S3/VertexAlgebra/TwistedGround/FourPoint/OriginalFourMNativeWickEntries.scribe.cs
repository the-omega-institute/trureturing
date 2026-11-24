using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMNativeWickEntriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeWickEntries.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native Wick entries at the four punctures",
        H("Signed covariance and charge-linear mean"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-four-m-native-wick-entries-ab-covariance"),
                DeclarationHandle.Create(Prefix + "nativeTaylor_ab"),
                H("Covariance in the A and B charts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an interior real chart argument, when the A or B slit parameter has norm less than one, "
                    + "each physical native covariance Taylor entry is the double inverse jet sum of the signed "
                    + "slit covariance entries, with a relative sign factor from each puncture."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-m-native-wick-entries-d-covariance"),
                DeclarationHandle.Create(Prefix + "nativeTaylor_d"),
                H("Covariance on the D lip"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At an interior real argument on the actual D lip, the covariance is the corresponding "
                    + "double inverse jet sum of the literal D lip entries, with the two D relative factors."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-m-native-wick-entries-ab-mean"),
                DeclarationHandle.Create(Prefix + "meanTaylor_ab"),
                H("Charge-linear mean in the A and B charts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any fixed charge, under the A or B interior and slit-parameter hypotheses, the physical "
                    + "singleton equals the inverse jet sum of slit mean entries times the charge bilinear and the "
                    + "relative factor of that puncture."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-m-native-wick-entries-d-mean"),
                DeclarationHandle.Create(Prefix + "meanTaylor_d"),
                H("Charge-linear mean on the D lip"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At an interior argument on the actual D lip, the fixed-charge singleton equals the "
                    + "corresponding inverse jet sum of the literal D lip means times the charge bilinear and D "
                    + "relative factor."))),
                DescribeRole.Theorem))));
}
