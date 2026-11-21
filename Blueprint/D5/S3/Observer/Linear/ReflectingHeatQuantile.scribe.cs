using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ReflectingHeatQuantileDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed quadrature errors for equal-mass bins of the canonical heat multiplier.",
        H("Signed right-endpoint quadrature"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflecting-heat-quantile-discrepancy-minimum"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatQuantile.discrepancy_le"),
                H("Kernels with one minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The density has unit mass in each bin. For a kernel that decreases to a minimum and then increases to zero, the right-endpoint sum minus its weighted integral is bounded above by minus the kernel at the minimum. On each finite prefix the bound telescopes from the minimum to the larger of the minimum location and the final endpoint. Absolute convergence passes the inequality to the half-line."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflecting-heat-quantile-discrepancy-antitone"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatQuantile.discrepancy_antitone"),
                H("Decreasing kernels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a kernel decreasing to zero, the lower and upper endpoint values bound the integral on each bin. The signed error on a finite prefix is between the difference of its terminal and initial endpoint values and zero. On the half-line the lower bound is minus the value at the initial endpoint."))),
                DescribeRole.Theorem))));
}
