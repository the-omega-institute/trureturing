using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones;
internal sealed class PhysicalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical banks for the upper union", H("Nested bit splits preserve every occurrence"),
        Blocks(
            Paragraph(Text("The terminal order is W,U,X,V. Bank 1 consists of all U positives and W mask p, followed by the W terminal. Bank 2 consists of all V positives, W mask H XOR p and X mask C, followed by the U terminal. Bank 3 consists of W mask F XOR H, followed by the X terminal. Bank 4 consists of X mask E XOR C, followed by the V terminal.")),
            Paragraph(Text("Increasing set-bit decoding maps each mask to actual labels at its chain offset. The nested split of F into p, H XOR p and F XOR H partitions every W positive exactly once; the split of E into C and E XOR C does the same for X. Together with U,V and the four terminals, the concatenated word is a permutation of List.range k, not just a list with the correct total mass.")),
            Paragraph(Text("The paired bank sums use the same decoded subsets in both rows: (uA+pL, uB+(H-p)L+CM, (F-H)L, (E-C)M) and the identical coefficients on (2A,Bn,Ln,Mn). All bank entries are nonnegative in each row. The pre word includes banks 1 and 2 and their terminals; the post word includes banks 3 and 4. Its literal cut is pre.length, where the true fresh label is inserted before bank 3."))), []));
}
