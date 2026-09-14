using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class PronyAbsoluteTargetStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite contractive moment data control absolute error over every future time.",
        H("Absolute target stability without separated modes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prony-absolute-target-error"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/GoldenTomography/"
                    + "PronyAbsoluteTargetStability.prony_target_absolute_error_bound"),
                H("All-time absolute error from an initial moment block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Consider two finite real exponential moment families with d and e nodes. "
                    + "Every node has absolute value at most theta, with 0 <= theta < 1. "
                    + "If their moment differences at all indices below q = d+e have absolute "
                    + "value at most epsilon >= 0, the complete error sequence is absolutely "
                    + "summable. Its sum is at most epsilon times "
                    + "q + (((1+theta)/(1-theta))^q - 1)/2. "
                    + "Signed and zero weights, repeated nodes, and arbitrarily small node gaps "
                    + "are permitted. The proof deflates one actual mode and bounds only the "
                    + "tail beyond the measured block. It never divides by a weight or node gap. "
                    + "The conclusion concerns the target sequence, not identification of "
                    + "individual hidden coordinates. The constant depends on q and the gap "
                    + "1-theta, although it does not depend on a time horizon."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction")),
        ]));
}
