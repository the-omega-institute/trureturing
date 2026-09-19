using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator.TranslationEnergy.Unit;

internal sealed class CertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational enclosure at log two.",
        H("A rational enclosure at log two"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unit-certificate-center-certificate"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate"),
                H("The exact rational center"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For the radius-one literal test with p=q=1 and rational shift 287209/414355, the actual rounded producer uses mesh depth 15, scalar precision 16 and Taylor depth 68. The full Boolean checker succeeds at requested binary precision 4.")),
                    Paragraph(Text("The value at zero is exactly 1+i. The actual rational aggregate endpoints enclose the full translation energy, the lower endpoint is strictly positive, and the width is at most 115/2048+5/268435456. This is strictly below 1/16. The positive lower endpoint follows from the analytic energy lower bound and the accepted width."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unit-certificate-log-two-certificate"),
                DeclarationHandle.Create("D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.log_two_certificate"),
                H("Two-sided logarithmic inflation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Define logTwoBox by subtracting 1152/10^10 from the actual center lower endpoint and adding the same amount to its upper endpoint. The resulting rational interval encloses the energy at the actual real shift log 2, has strictly positive lower endpoint and width strictly less than 1/16.")),
                    Paragraph(Text("The shift-transfer coefficient specializes to 1152, and Real.log_two_near_10 bounds the center error by 10^-10. The total inflation is 2304/10^10. The theorem also retains the exact value at zero and the successful full center check."))),
                DescribeRole.Theorem)),
        []));
}
