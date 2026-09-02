using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerTails;

internal sealed class PrimeDepthSummabilityWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extraction depth moves the exact summability boundary of the scalar prime tail.",
        H("Prime Extraction-Depth Summability Window"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-depth-weight-summable-iff"),
                DeclarationHandle.Create("D5/S3/Analytic/EulerTails/PrimeDepthSummabilityWindow.prime_depth_weight_summable_iff"),
                H("The depth threshold is N sigma greater than one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For prime weights p raised to minus depth times sigma, summability over all primes holds exactly when depth times sigma is greater than one.")),
                    Paragraph(Text(
                        "The theorem directly reuses Mathlib's exact prime-rpow criterion. It controls a scalar majorant and does not assert an Euler product identity, logarithmic weighting, or analytic continuation."))),
                DescribeRole.Theorem))));
}
