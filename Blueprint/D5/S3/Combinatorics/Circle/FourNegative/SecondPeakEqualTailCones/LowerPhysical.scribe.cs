using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones;
internal sealed class LowerPhysicalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower-cone physical permutation", H("The complementary W mask stays in bank four"),
        Blocks(
            Paragraph(Text("For 2<=a<s and b>=2s+1, use the native ceiling C and capacity F from LowerCeiling. Bank 1 is all U positives followed by W terminal. Bank 2 is all X positives and W mask C, followed by U terminal. Bank 3 is all V positives followed by X terminal. Bank 4 is W mask F XOR C followed by V terminal.")),
            Paragraph(Text("The exact split C together with F XOR C partitions all W positive occurrences. Complete positive chains and the four terminals account for every other occurrence. The resulting concatenation is a permutation of List.range k with actual chain-offset labels. In both centered rows every bank entry is nonnegative.")),
            Paragraph(Text("The old positive bank masses are (uA, EM+CL, uB, (F-C)L), and the enlarged masses use the same coefficients on (2A,Mn,Bn,Ln). The pre word comprises the first two banks and terminals; post comprises the last two. Its length determines the literal insertion cut. No W complement is moved to bank 3, so the physical inventory matches the lower seam allocation exactly."))), []));
}
