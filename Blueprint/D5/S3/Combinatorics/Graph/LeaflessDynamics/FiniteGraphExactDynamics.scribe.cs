using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LeaflessDynamics;

internal sealed class FiniteGraphExactDynamicsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphExactDynamics.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classification of exact finite positive expansivity on simple graphs",
        H("Classification of exact finite positive expansivity on simple graphs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("leafless-simple-graph-exact-map"),
                DeclarationHandle.Create(Owner + "exists_exact_edgeWalkMap"),
                H("A piecewise affine exact positively expansive map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each source edge traverses its reduced all-edge walk at constant speed and fixes its endpoints. The closed-cell maps agree on overlaps. Contracting inverse branches prove exactness, and distinct image germs at cell boundaries give uniform expansion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("simple-graph-leafless-classification"),
                DeclarationHandle.Create(Owner + "exists_exact_finitelyPositiveExpansive_iff"),
                H("Degree one characterizes the obstruction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nontrivial finite connected simple graph admits a continuous topologically exact finitely positively expansive map precisely when no vertex has degree one. A degree-one vertex gives a pendant arc and rules out every finite Bowen bound."))),
                DescribeRole.Theorem))));
}
