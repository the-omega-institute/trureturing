using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePositiveRationalGoldenTomographyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct positive rational scales have distinct lifted golden nodes and faithful finite time tomography.",
        H("Finite Positive-Rational Golden Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-positive-rational-golden-time-window-injective"),
                DeclarationHandle.Create("D5/S3/Analytic/GoldenTomography/FinitePositiveRationalGoldenTomography.finite_positive_rational_golden_time_window_injective"),
                H("Lifted golden time windows recover finite rational-scale amplitudes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An injective finite family of positive rational scales remains injective after passage to the existing lifted golden logarithmic coordinate.")),
                    Paragraph(Text(
                        "Vandermonde tomography then reconstructs the hidden amplitudes exactly. The result concerns the universal-cover coordinate and does not assert quotient-circle conditioning."))),
                DescribeRole.Theorem))));
}
