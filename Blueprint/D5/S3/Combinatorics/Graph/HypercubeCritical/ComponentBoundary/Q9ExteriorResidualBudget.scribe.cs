using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9ExteriorResidualBudgetDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ExteriorResidualBudget";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exterior residual demands of a balanced cube support",
        H("Exterior residual demands of a balanced cube support"),
        Blocks(
            Describe.Lean(DescribeId.Create("weighted-exterior-residual-budget"),
                DeclarationHandle.Create(Module + ".weighted_exterior_residual_budget"),
                H("Exterior cancellation bounds the completion size"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The Huang action on the full cube extends the switching vector of an induced balanced cubic component to a three-eigenvector. Its exterior rows vanish. If a partial selection has already contributed a signed residual to an exterior row, every remaining selected neighbor contributes a unit in magnitude.")),
                    Paragraph(Text("Assign nonnegative weights to the exterior rows. Summing their weighted absolute residuals bounds the required total weighted incidence from the remaining support. A uniform upper bound on the weighted incidence of each remaining vertex then bounds the number of vertices needed. This provides a dual test for partial shell completions in Hong–Wu–Xia Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation"))]));
}
