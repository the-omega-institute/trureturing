using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSecond;

internal sealed class KernelLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit explicit majorant for the correction to the power-kernel integral.",
        H("Explicit power-kernel correction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("correction-majorant"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit.correctionMajorant"),
                H("Correction majorant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The majorant is pi^2/(6*(1-pi^2/(6*s^2))). Its denominator is positive for s at least pi."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kernel-correction-upper"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit.kernel_correction_upper"),
                H("Cubic sine bound for the correction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real s at least pi, s*(pi/sin(pi/s)-s) is nonnegative and at most the correction majorant. The cubic lower bound for sine preserves the coefficient one sixth."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("majorant-limit"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/KernelLimit.correction_majorant_limit"),
                H("Explicit limiting majorant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The correction majorant tends to pi^2/6 as s tends to positive infinity. This coefficient controls the localized prime-weight upper estimate. A matching lower bound for the second distinct-prime counting threshold is not established here."))),
                DescribeRole.Theorem))));
}
