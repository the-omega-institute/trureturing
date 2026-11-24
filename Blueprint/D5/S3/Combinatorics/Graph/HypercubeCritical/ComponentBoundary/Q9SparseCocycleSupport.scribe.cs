using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SparseCocycleSupportDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseCocycleSupport";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The possible sparse pivot graphs",
        H("The possible sparse pivot graphs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-sparse-cocycle-support"),
                DeclarationHandle.Create(Module + ".sparse_cocycle_support"),
                H("The possible sparse pivot graphs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The degree cap and the forced triples leave a three-spoke star or a "
                        + "four-cycle. Each edge has two forced triples containing it, exhausting "
                        + "its pair cap. This gives counts of six or eight triples outside the pivot."))),
                DescribeRole.Theorem)),
        []));
}
