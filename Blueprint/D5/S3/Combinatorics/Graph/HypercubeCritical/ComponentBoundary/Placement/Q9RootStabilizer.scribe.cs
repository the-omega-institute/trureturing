using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9RootStabilizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cube translations and coordinate permutations compose as a cube normalization. The same transformations preserve the degree of every induced support.",
        H("Composition of cube normalizations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalize-comp"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9RootStabilizer.normalize_comp"),
                H("Composition of cube normalizations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Cube translations and coordinate permutations compose as a cube normalization. The same transformations preserve the degree of every induced support."))),
                DescribeRole.Theorem)),
        []));
}
