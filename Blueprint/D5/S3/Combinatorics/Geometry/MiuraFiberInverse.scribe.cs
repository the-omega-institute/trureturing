using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraFiberInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraFiberInverse.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual core and occupied lines recover every value.", H("The actual core and occupied lines recover every value"),
        Blocks(
            Describe.Lean(DescribeId.Create("miurafiberinverse-0"),
                DeclarationHandle.Create(Prefix + "same_core_same_active_equal"), H("Complete function recovery"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix two normalized unit-edge arrays on the same rectangle, each in the exact residual class with a minima and b maxima. Suppose both legally reduce to the same individual core function, with no adjacent frozen lines on either axis. If their occupied columns and occupied rows agree at every physical coordinate, the complete height functions agree. Delete an adjacent frozen pair at the same position in both arrays. Exact extremum transport preserves the agreement of occupied coordinates. Normalization and actual core uniqueness ensure that both contracted arrays still reduce to the given core. Induction identifies these smaller complete functions. The frozen slope surviving at the seam identifies the signed step of the deleted line, and the signed restore inverse recovers every cell. If no adjacent pair remains on either axis, both arrays are already the same actual reduced core."))), DescribeRole.Theorem))));
}
