using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class CyclicHyperbolicSectorSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate and seam support for cyclic hyperbolic sector metrics.",
        H("Cyclic hyperbolic sector support"),
        Blocks(
            Paragraph(Text("This support module gives the explicit cylindrical coordinates, actual face rotations, sector membership, and finite-chain folding lemmas used by the cyclic sector metric. The definitions preserve source tags, repeated seams, axis points, and arbitrary total angular period; the metric theorem is stated in the companion module.")))));
}
