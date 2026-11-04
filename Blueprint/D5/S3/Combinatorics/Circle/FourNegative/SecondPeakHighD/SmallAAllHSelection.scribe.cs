using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD;
internal sealed class SmallAAllHSelectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unbounded small-a selection", H("Unbounded small-a selection"),
        Blocks(
            Paragraph(Text("For every a=3 or a=4, P>=2, Q>=1 and H>=2, the selector constructs natural v,m,M and before=true with Submask m M and exact HighD rowBounds (2^a) (2^P) (2^Q) (2^H). Splitting 2^H=4*2^(H-2) transports every certified mask, while U=2^(H-2)-1 activates the universal positive polynomial families. The unrestricted mod-72 decomposition covers a=3, p=4 or 8 and q>=8. Eight boundary families cover the remaining small q, and the signed ceiling and parity remainder cover the universal large-p tails. All branches refer to the same old and charged new heads. This selector is a component of the Circle construction; physical packet and full endpoint joins remain separate obligations.")),
            Describe.Lean(DescribeId.Create("highd-smallaallhselection-small-a-selection"), DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/SmallAAllHSelection.small_a_selection"), H("small_a_selection"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Consumed in the construction described here, with the exact telescope supplied by Lean."))), DescribeRole.Theorem)), []));
}
