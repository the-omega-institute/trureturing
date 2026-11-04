using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum;
internal sealed class BorrowArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unbounded borrow windows", H("Natural selectors and actual bits"),
        Blocks(Paragraph(Text("For 2<=b<a<s, borrow_selector_windows proves the actual natural selectors' bounds, literal testBit containment, and all U/V/W old/new windows. When s=a+1 it uses u=0 and t=2 for a=b+1, otherwise t=quotientT-1. The corrected W identities are K-1-2G=2x-y and Gp=4x^2*y+y-2x-1. In the far case it first proves quotientT>=2p+1 for p=2^(s-a-1), then supplies the p-bit by actual binary borrowing. The integer division and natural subtraction casts are explicit; no feasibility certificate is assumed. The fresh indicators include an insertion before V when checking W. The shifted polynomial certificates cover unbounded cones; their finite expressions are not parameter sampling."))), []));
}
