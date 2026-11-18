using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSecond;

internal sealed class ContinuumWeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The continuum moving-weight integral preserves the exact power-kernel cancellation.",
        H("Continuum correction at a moving cutoff"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("central-integral-upper"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/ContinuumWeight.central_integral_upper"),
                H("Central continuum mass upper bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every P>0 and s>1, the integral over [P/2,2P] of log(1+exp(-s*abs(log(t/P)))) is at most P*(pi/sin(pi/s)-s)+(s/2+2)*P*2^(-s). The power-kernel integral is evaluated exactly before subtracting the linear ramp.")),
                    Paragraph(Text("The remaining endpoint and removed-tail terms decay geometrically. The explicit upper majorant for the normalized kernel correction tends to pi^2/6. This supports the second-threshold counting upper bound; a matching lower bound is not established here."))),
                DescribeRole.Theorem))));
}
