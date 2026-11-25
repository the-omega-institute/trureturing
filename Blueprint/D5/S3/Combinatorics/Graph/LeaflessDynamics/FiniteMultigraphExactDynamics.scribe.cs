using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LeaflessDynamics;

internal sealed class FiniteMultigraphExactDynamicsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteMultigraphExactDynamics.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact positive expansivity on finite multigraph realizations",
        H("Exact positive expansivity on finite multigraph realizations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("leafless-multigraph-exact-map"),
                DeclarationHandle.Create(Owner + "exists_exact_positivelyExpansive"),
                H("Exact positive expansivity on the original graph"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three-segment subdivision preserves connectivity and the incidence count condition. Its affine edge-walk map transports through the proved homeomorphism to any metric realization of the original graph, with loops and parallel edges allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-multigraph-exact-expansivity-classification"),
                DeclarationHandle.Create(Owner + "exists_exact_finitelyPositiveExpansive_iff"),
                H("The degree-one obstruction gives a complete classification"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite connected graph with at least one edge admits a continuous topologically exact map with a finite forward Bowen bound if and only if no vertex has exactly one incident flag. The constructive direction gives positive expansivity. For the converse the subdivision homeomorphism transports a pendant arc back to the original graph, where it obstructs every finite Bowen bound."))),
                DescribeRole.Theorem))));
}
