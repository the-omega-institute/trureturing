using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9EightfoldCoverLocalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverLocal.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The eightfold corner rule",
        H("The eightfold corner rule"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-eightfold-corner-rule"),
                DeclarationHandle.Create(Prefix + "eightfold_corner_rule"),
                H("The eightfold corner rule"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Consider an exterior cube edge whose eight transverse translates are "
                        + "all edges of a Huang-balanced cubic support.")),
                    Paragraph(Text("The exterior eigenrow has four positive and four negative terms. The "
                        + "edge transports all eight signs by a common factor. An opposite-sign "
                        + "pair contributes exactly one selected corner across the two layers, "
                        + "while an equal-sign pair contributes none.")),
                    Paragraph(Text("Anticommutation supplies the sign test, square exclusion prevents "
                        + "double occupancy, and the cubic degrees exhaust the four possible "
                        + "opposite-sign partners. Hence there are exactly sixteen selected "
                        + "corners."))),
                DescribeRole.Theorem)),
        []));
}
