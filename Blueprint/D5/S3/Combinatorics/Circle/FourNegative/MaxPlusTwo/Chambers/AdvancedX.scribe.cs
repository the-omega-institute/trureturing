using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers;
internal sealed class AdvancedXDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Advancing physical X-positive labels",
        H("Exact physical source and charge"),
        Blocks(Paragraph(Text("Moving a selected X mask before the third negative preserves the physical inventory. It subtracts 2e3 times that mask from the third reserve and Cprime times that mask from the remaining charge. The actual source criterion retains both changes. Its descending c=2,a=b+1 consumer advances mask one, including the coincident T=4 mask boundary."))), []));
}
