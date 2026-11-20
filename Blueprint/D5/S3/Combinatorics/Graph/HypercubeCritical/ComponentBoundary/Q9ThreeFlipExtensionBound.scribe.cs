using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9ThreeFlipExtensionBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-coordinate translate cannot occur in a 258-vertex candidate",
        H("A three-coordinate translate cannot occur in a 258-vertex candidate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-three-flip-extension-bound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ThreeFlipExtensionBound.card_le_256_of_three_flip_translate"),
                H("Three flipped coordinates leave room for at most 256 vertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let U induce maximum degree at most three in the nine-cube. If U contains a connected Huang-balanced cubic component and its translate by three coordinate flips, then U has at most 256 vertices.")),
                    Paragraph(Text("The signed coordinate action forces 48 occupied fibres over the six fixed coordinates, with 24 on each parity side. Each occupied fibre contains an edge of the component and its antipodal edge. Closedness forbids every other pattern in those fibres.")),
                    Paragraph(Text("The projected parity equation gives even residual neighbor counts. Every residual fibre touches an occupied fibre, so at most four patterns can survive there as well. The fibre bound applies to arbitrary U."))),
                DescribeRole.Theorem)),
        []));
}
