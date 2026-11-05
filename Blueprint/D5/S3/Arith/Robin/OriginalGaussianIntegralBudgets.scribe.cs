using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalGaussianIntegralBudgetsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original localization budgets on their exact domains.",
        H("The original localization budgets on their exact domains"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-gaussian-central-budget"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/OriginalGaussianIntegralBudgets.central_original"),
                H("The original localization budgets on their exact domains"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text("For m>=1 and gamma>10, b(y)=(4*y+11)*exp(y/2). The exact central positive integral over (0,infinity) obeys integral b*V<=300*m*(gamma+10)^2*exp(33*m/4). Tilting moves the normalized Gaussian center to 17*m. A positive quartic majorant integrates to 2*exp(33*m/4)*(85*m*(gamma^2+2)+93), using the attributed existing second and fourth moments.")),
                Paragraph(Text("On [0,infinity) outside the CLOSED interval [4*m,28*m], tilting by exp(y) moves the center to 18*m. The exterior has squared distance at least 100*m^2 from that center. Splitting the exponent supplies exp(-25*m/2), which combines with exp(17*m) to give exp(9*m/2). The exact exterior integral of abs(Re(H))*V is at most 12*(gamma+10)^2*exp(9*m/2).")),
                Paragraph(Text("On the ENTIRE negative axis, squared distance from 16*m is at least 256*m^2. The Gaussian split supplies exp(-32*m), and the integral of abs(Re(H))*V is at most 8*(gamma+10)^2*exp(-32*m). Global product integrability is proved before these restrictions; it includes the sign change of b on the negative axis.")),
                Paragraph(Text("The complement identity is [4*m,28*m]^c=([0,infinity)\\[4*m,28*m]) union (-infinity,0), with disjoint pieces. Both closed endpoints remain central. The change from [0,infinity) to (0,infinity) uses only the zero-measure singleton endpoint. OriginalPositiveUPeak consumes all three budgets and these exact domain facts together with the separate full signed-HV budget."))),
                DescribeRole.Theorem))));
}
