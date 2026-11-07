using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones;
internal sealed class DyadicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eight exact dyadic coordinate rows", H("Transport of all mask coordinates"),
        Blocks(
            Paragraph(Text("The chart table has eight rows and eleven slots: x,y,z,z/2,y/z,y/(2z),y/z^2,x/(2z),y/2,x/2,lambda. Each slot is an integer monomial in chart variables u,v,w, so no division is performed inside a polynomial gate proof. The associated epsilon row is (0,w,vw,0,v,4u^2v,2uv^2w,uv), and the adaptive delta row is (1,1,1,0,0,1,1,1).")),
            Paragraph(Text("The actual row uses powers 2^a,2^b,2^s,2^(s-1),2^(b-s),2^(b-s-1),2^(b-2s),2^(a-s-1),2^(b-1),2^(a-1),2^(b-a-1). Natural exponent equalities are proved before translating these powers into monomials. Under s>=2, a>=s+1, b>=a+1 and b>=2s, equality of the eleven slots plus the epsilon and delta identities transports the entire native allocation matrix to the selected chart.")),
            Paragraph(Text("This is the interface between natural-gap case splitting and integer ring positivity. It preserves the actual W and X masks, including the zero X allocation on the first low-a boundary; it does not create a new ordering theorem."))), []));
}
