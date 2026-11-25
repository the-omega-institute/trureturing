using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMDLipReflectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipReflection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schwarz reflection of the native signed D-lip germs",
        H("Joint reflection at the D boundary"),
        Blocks(
            Describe.Lean(DescribeId.Create("fourm-d-lip-mean-reflection"),
                DeclarationHandle.Create(Prefix + "dLipMean_upper_reflection"),
                H("Reflection of the signed mean"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either external sign and real t > 1, the upper mean near "
                    + "(0,t) equals the conjugate of the lower mean at the conjugate pair. The "
                    + "inverse square root stays on its principal branch and conjugation exchanges "
                    + "the two explicit lip phases."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-d-lip-covariance-joint-reflection"),
                DeclarationHandle.Create(Prefix + "dLipCovariance_upper_reflection_joint"),
                H("Reflection of the full covariance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each real t > 1 and all leg and sign choices, the upper "
                    + "covariance near (0,0,t) equals the conjugate of the lower covariance evaluated "
                    + "at the conjugates of both local coordinates and of the D parameter. Differentiate "
                    + "the Euler D-period reflection to transport r(1−r)P′(r)/P(r). Apply the mean "
                    + "reflections to the weighted denominator and keep the Cauchy term for opposite "
                    + "external signs on the same leg. The mixed-leg rational kernel is conjugated in "
                    + "its own branch."))),
                DescribeRole.Theorem))));
}
