using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LeaflessDynamics;

internal sealed class FiniteGraphTransitiveValenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp finite positive expansivity for transitive finite graphs",
        H("Sharp finite positive expansivity for transitive finite graphs"),
        Blocks(Describe.Lean(
            DescribeId.Create("transitive-multigraph-sharp-valence-bound"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/LeaflessDynamics/FiniteGraphTransitiveValence.forwardBowenBound_of_transitive_multigraph"),
            H("A transitive map has forward Bowen order at most one below the maximum valence"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let a finite connected graph with at least one edge have maximum valence at most D, with D at least two. A continuous topologically transitive finitely positively expansive self-map has a positive scale at which each forward Bowen ball has at most D minus one points. Loops count twice in the valence.")),
                Paragraph(Text("The forward images of an arc in a nonempty open set miss at most a finite totally invariant set, which finite positive expansivity and transitivity force to be empty. This gives pointwise strong transitivity and allows the two-arm count in the affine subdivision to be transported to the original graph. The parallel-edge construction attains the bound for every D at least three."))),
            DescribeRole.Theorem))));
}
