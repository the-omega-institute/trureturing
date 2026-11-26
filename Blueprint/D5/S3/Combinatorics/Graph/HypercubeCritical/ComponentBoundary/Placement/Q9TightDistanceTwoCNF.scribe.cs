using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9TightDistanceTwoCNFDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9TightDistanceTwoCNF.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized opposing-star geometry supplies the inputs of the distance-two refutations.",
        H("Geometric clauses for opposing stars"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("odd-exterior-pair-clause"),
                DeclarationHandle.Create(Owner + "oddExteriorPairClause"),
                H("Geometric clauses for opposing stars"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polarity and ordered neighbor clauses reuse the signed cube support rules. For a contact starting at odd parity, a two-axis displacement containing an exterior axis would be outside the tight family. This supplies the forbidden cross-support clause needed by the certificates."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9TightDistanceTwoNormalized")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9SharedContactCNF"))
        ]));
}
