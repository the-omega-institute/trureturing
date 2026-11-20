using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9EightfoldCoverSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct eightfold edges have disjoint selected shells",
        H("Distinct eightfold edges have disjoint selected shells"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-eightfold-cover-shells-disjoint"),
                DeclarationHandle.Create(Prefix + "eightfold_cover_shells_disjoint"),
                H("Distinct eightfold edges have disjoint selected shells"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every endpoint of one eightfold cover is at Hamming distance at "
                        + "least four from each endpoint of another for the same support.")),
                    Paragraph(Text("A distance-two pair would give opposite sign products by the "
                        + "negative square, but equal products by the corner rule. At distance "
                        + "three two directions have the same phase and force an extra exterior "
                        + "neighbor.")),
                    Paragraph(Text("The distance bound separates the transverse first shells from each "
                        + "other and from the other second shell. A shared second-shell vertex "
                        + "would have two selected neighbors in each disjoint first shell, "
                        + "contradicting cubicity."))),
                DescribeRole.Theorem)),
        []));
}
