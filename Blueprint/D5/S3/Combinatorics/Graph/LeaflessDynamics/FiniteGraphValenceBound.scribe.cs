using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LeaflessDynamics;

internal sealed class FiniteGraphValenceBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A valence bound for forward Bowen balls on finite graphs",
        H("A valence bound for forward Bowen balls on finite graphs"),
        Blocks(Describe.Lean(
            DescribeId.Create("strong-transitivity-sharp-valence-bound"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphValenceBound.forwardBowenBound_of_stronglyTransitive"),
            H("Forward Bowen order at most one below the maximum valence"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let the maximum valence of a nontrivial connected finite graph be at most D, with D at least two. A continuous strongly transitive finitely positively expansive map has a uniform positive radius at which each forward Bowen ball contains at most D minus one points.")),
                Paragraph(Text("Strong transitivity supplies an image passing through each vertex from an open edge. The absence of folds in the open edge gives an immersed path whose image contains two incident arms at the vertex. Distinct points on that path separate at a uniform scale. Each remaining arm can contribute at most one point at that scale. Away from vertices the entire Bowen ball lies in a short edge interval and contains at most one point."))),
            DescribeRole.Theorem))));
}
