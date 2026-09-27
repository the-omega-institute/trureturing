using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ThreeColorSmallMixedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ThreeColorSmallMixed.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite properly three-colored simple graph whose mixed vertices all have degree two and whose mixed population has size between two and five has reciprocal deletion potential at least two.",
        H("Small mixed graph inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("small-mixed-graph-potential"),
                DeclarationHandle.Create(Prefix + "small_mixed_graph_potential"),
                H("Actual graph theorem"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For an arbitrary finite simple graph with a proper coloring by Fin 3, assume every mixed vertex has degree exactly two and that the mixed vertex count lies between two and five. Then ColoredReciprocalDeletion.potential is at least two. Isolates and empty color classes are allowed, and there is no bound on the ordinary populations or graph size.")),
                    Paragraph(Text("The proof deletes isolates only in the accounting argument, transfers the mixed populations to the finite-set incidence API, applies the substantive small_population_bound certificate, and restores the isolated vertices with the reciprocal monotonicity estimate. The public theorem has only graph, coloring, degree, and mixed-count hypotheses."))),
                DescribeRole.Theorem)),
        []));
}
