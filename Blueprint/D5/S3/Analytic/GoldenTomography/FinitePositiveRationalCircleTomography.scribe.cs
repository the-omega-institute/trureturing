using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePositiveRationalCircleTomographyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite positive rational golden circle nodes admit exact moment and time tomography.",
        H("Finite Positive-Rational Circle Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-positive-rational-circle-time-window-injective"),
                DeclarationHandle.Create("D5/S3/Analytic/GoldenTomography/FinitePositiveRationalCircleTomography.finite_positive_rational_circle_time_window_injective"),
                H("Distinct quotient-circle nodes are recovered from time samples"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An injective finite family of positive rational scales gives pairwise distinct complex golden circle nodes. The first matching scalar time window then uniquely recovers all modal amplitudes.")),
                    Paragraph(Text(
                        "The argument composes quotient-circle injectivity with the existing finite Vandermonde and crystal time-frequency theorems. It remains a finite exact result and does not claim uniform conditioning."))),
                DescribeRole.Theorem))));
}
