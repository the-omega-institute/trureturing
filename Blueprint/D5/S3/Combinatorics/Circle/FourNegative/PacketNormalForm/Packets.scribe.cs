using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm;
internal sealed class PacketsDocument : IScribeDocumentDefinition
{
 public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Seam and peak checks for physical packets", H("Endpoint data"), Blocks(Paragraph(Text("A packet check contains only its post-negative nonnegativity and pre-negative upper bound, followed by the checks of subsequent packets. Four negative labels give four pairs per row. Nonnegative packet steps imply all internal bounds in any order. The fresh ear can slide right within its current packet, preserving the same old word."))), []));
}
