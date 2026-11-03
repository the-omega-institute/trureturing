using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD;
internal sealed class LowBitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Low bits of a dyadic predecessor", H("Low bits of a dyadic predecessor"),
        Blocks(
            Describe.Lean(DescribeId.Create("secondpeakhighd-lowbits-bit-below"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.bit_below"),
                H("bit below"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of low bits of a dyadic predecessor. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("secondpeakhighd-lowbits-submask-of-land"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_of_land"),
                H("submask of land"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of low bits of a dyadic predecessor. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("secondpeakhighd-lowbits-submask-predecessor"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/LowBits.submask_predecessor"),
                H("submask predecessor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A consumed part of low bits of a dyadic predecessor. The complete module scope and assumptions are stated below."))), DescribeRole.Theorem),
            Paragraph(Text("Submask m M means every true testBit of m is true in M. A bit of m<2^k lies below k. The existing private multiple_predecessor_bits lemma proves that every position below k is true in 2^k*n-1 for n>=1. These two statements supply submask_predecessor; small_proper_predecessor additionally obtains strict m<M when n>=2.")),
            Paragraph(Text("The land equality m &&& M=m gives the same bit inclusion and is used only for the twenty genuinely finite h=4 rows. No finite test is used to infer an unbounded dyadic family."))), []));
}
