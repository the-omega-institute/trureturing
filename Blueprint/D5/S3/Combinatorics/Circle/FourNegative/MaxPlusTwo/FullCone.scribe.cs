using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo;
internal sealed class FullConeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical chamber realization of the max-plus-two construction",
        H("The strict rising valley"),
        Blocks(Paragraph(Text("For 2<=b<a<c, the minimal fourth gap is d=c+2. Put R=2^a, T=2^b, Z=2^c, p=Z/(2R) and q=Z/(2T). The exact constructor uses masks u1=3, u2=u3=v0=w=0, v2=p+q and v3=p. The dyadic ratios make p and q distinct binary positions, so v3 is a submask of v2 and all masks fit their physical positive chains. valley_rising_inventory proves that this actual baseWord uses every physical label once. valley_rising_strong applies the actual centered-source block criterion with reserves 3A, 2e1(p+q) and 2e1p. The polynomial bounds place each reserve between ej and 2ej-A, and nonnegative actual charge relates these bounds to the exact remaining-charge bounds of ActualBlocks.four_reserve_strong.")),
            Paragraph(Text("The full max-plus-two statement has independent a,b,c>=2 and d>=max(a,b,c)+2, with one physical sigma satisfying OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,0)). The complete cone remains OPEN: its other constructor chambers and their assembly into this public endpoint are not supplied by the strict rising-valley result. The unrestricted four-gap joint-order problem also remains OPEN."))), []));
}
