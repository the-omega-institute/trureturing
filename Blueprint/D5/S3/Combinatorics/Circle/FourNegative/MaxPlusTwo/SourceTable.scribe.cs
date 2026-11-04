using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo;
internal sealed class SourceTableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four independent centered ladders",
        H("The actual old and enlarged source"),
        Blocks(
            Paragraph(Text("For all independent a,b,c,d>=2, write R=2^a,T=2^b,Z=2^c,D=2^d, m=RTZ, C=RT+R+1, A=m+C and N=Dm-1. The internal source_table proves the centered reductions on the four actual label intervals starting at 0,d,d+c,d+c+b. The successive old ladder bases are A,DC+1,D(R+1)Z+Z+1,DTZ+TZ+T+1. The enlarged-source bases are twice these old bases minus 0,1,Z+1,TZ+T+1, respectively. Each final label has the exact negative centered value. The fresh physical label has enlarged-source value A.")),
            Paragraph(Text("The proof applies the existing centered_shift and centered_ladder at their actual types, proving positivity, odd modulus, base bounds and all four recurrences at these weaker fourth-gap hypotheses. It does not invoke the eventual construction or its stronger d>=a+b+c+3 premise.")),
            Paragraph(Text("This helper identifies source values on physical occurrences. It supplies no permutation or joint-order existence by itself; unrestricted Circle C3.1 and the complete max-plus-two construction remain separate obligations."))), []));
}
