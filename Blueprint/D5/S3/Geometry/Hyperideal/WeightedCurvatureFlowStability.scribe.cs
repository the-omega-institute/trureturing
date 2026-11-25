using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class WeightedCurvatureFlowStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive trajectories of a multiplicatively weighted monotone field have quantitative pairwise stability without assuming local Lipschitz regularity of the field.",
        H("Pairwise stability of length-weighted curvature descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-curvature-flow-stability"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/WeightedCurvatureFlowStability.weighted_stability"),
                H("A square-root distance bound for the weighted flow"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Use the chart z=2 sqrt(length) on each positive coordinate. The coordinate-square identity splits the two-point derivative into ordinary length-space monotonicity and a diagonal term involving the sum of the two residuals.")),
                    Paragraph(Text("A one-sided lower bound of minus C on those residuals gives a squared chart distance growth factor exp(C times elapsed time). The chart distance separates positive lengths, so identical initial lengths give uniqueness among existing trajectories.")),
                    Paragraph(Text("This is a differential comparison for existing trajectories. It neither constructs solutions nor formalizes the extension of hyperideal covolume, the three interval Hessian certificates, or general degree-seven realization."))),
                DescribeRole.Theorem))));
}
