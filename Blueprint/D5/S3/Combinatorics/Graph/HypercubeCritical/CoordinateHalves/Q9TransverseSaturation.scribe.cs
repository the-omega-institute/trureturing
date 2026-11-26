using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9TransverseSaturationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TransverseSaturation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transverse incidences in cubic nine-cube supports",
        H("Transverse incidences in cubic nine-cube supports"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-minority-transverse-saturation"),
                DeclarationHandle.Create(Module + ".no_cubic_minority_transverse_saturation"),
                H("A minority edge cannot meet all transverse directions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Count each induced edge in a coordinate direction at its endpoint with that coordinate false. If each chosen parity class has one or four edges, the four transverse incidences from one size-four axis force all classes to have size four. The incidences from every other axis then exhaust each class. A single edge would meet eight transverse directions, whereas the two endpoints have only four incident edges besides their common edge.")),
                    Paragraph(Text("In Hong, Wu and Xia's separated 120+138 branch, the signed contact-block classification supplies two K4,4 covers for a 16+4 fold. In each cover and transverse direction, two contacts occur in each axial layer, which supplies two edges of each parity. The two covers together give the four incidences required by the theorem. The classification and its search completeness are inputs to this application. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
