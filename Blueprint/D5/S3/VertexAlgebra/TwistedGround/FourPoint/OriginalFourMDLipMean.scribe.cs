using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMDLipMeanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native signed mean at the D-channel boundary",
        H("Local branch and adjacent slit germ"),
        Blocks(
            Describe.Lean(DescribeId.Create("fourm-d-lip-mean"),
                DeclarationHandle.Create(Prefix + "dLipMean"),
                H("D-lip half-current source"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive sign keeps the slit mean. The negative sign uses the "
                    + "principal inverse square root of −h/b with factor b⁻¹ and the lip phase. "
                    + "That phase is −i for the lower D lip and +i for the upper D lip."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourm-d-lip-mean-analytic"),
                DeclarationHandle.Create(Prefix + "dLipMean_joint_analytic"),
                H("Holomorphic germ at the D boundary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At (0,t) for real t > 1, either lip formula is jointly analytic "
                    + "in the external variable and radial parameter. The reflected branch argument "
                    + "for the negative sign is t−1 at the centre."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-d-lip-mean-agreement"),
                DeclarationHandle.Create(Prefix + "dLipMean_eventuallyEq"),
                H("Agreement on the designated open lip"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each fixed r on the chosen open D lip, the D-lip mean agrees "
                    + "with the slit mean on a neighborhood of u = 0. The imaginary part of h/b "
                    + "retains its sign near that centre, where the inverse half-power phase identity applies."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-d-lip-weighted-nonzero"),
                DeclarationHandle.Create(Prefix + "dLipWeighted_sum_ne_zero"),
                H("Nonvanishing of the sum of weighted means"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At t > 1 the weighted means are 1 for the positive sign and "
                    + "a nonzero purely imaginary number for the negative sign. Equal signs give "
                    + "twice the same nonzero factor, and mixed signs give real part 1."))),
                DescribeRole.Theorem))));
}
