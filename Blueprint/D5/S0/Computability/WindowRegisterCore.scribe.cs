using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class WindowRegisterCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed binary register tracks and copying.",
        H("Fixed binary register tracks and copying"),
        Blocks(
            Paragraph(Text("Four separate register tracks have indices two through five. A register has a fixed origin marker, little-endian unit-bit symbols, an explicit end marker and blank cells beyond the end. The packed work tape stays on track one and the original input on track zero.")),
            Paragraph(Text("Copying reads a selected bit from each actual packed column and writes it to the target. Every read, write and head move is separate. The frame retains all unrelated tape cells and head positions while bounding both active heads.")),
            Describe.Lean(DescribeId.Create("copy-prefix"), DeclarationHandle.Create("D5/S0/Computability/WindowRegisterCore.copy_prefix"), H("copy prefix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: copy_prefix (m h j) (pre bs : List Bits) (L : \u2115) (hL : pre.length+bs.length \u2264 L) : run (config m h j (pre++bs) ((pre.map (select j)).map Symbol.unit) (pre.length+1) (pre.length+1) (.scan j)) (4*bs.length) = config m h j (pre++bs) (((pre++bs).map (select j)).map Symbol.unit) (pre.length+bs.length+1) (pre.length+bs.length+1) (.scan j) \u2227 \u2200 n \u2264 4*bs.length, Frame m h j (pre++bs) L (run (config m h j (pre++bs) ((pre.map (select j)).map Symbol.unit) (pre.length+1) (pre.length+1) (.scan j)) n)"))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/WindowAcquisitionPacked"))]));
}
