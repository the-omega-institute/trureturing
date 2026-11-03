using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird;
internal sealed class SelectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exhaustive large-third physical selection", H("Original labels and exact unbounded domain"),
        Blocks(Paragraph(Text("For b<a use terminal order W,V,X,U and banks U(full), X(full), W(full)++V(v), V(full XOR v), with fresh immediately before nX. For b=a and d>=a+2 use V,W,X,U and banks U(full), W(full), X(full)++V(v), V(full XOR v), inserting fresh before nX. For b=a,d=a+1 use V,W,X,U and banks U(full), W(full)++V(p), X(full)++V(v XOR p), V(full XOR v), inserting fresh before nW.")),
                    Paragraph(Text("The adjacent diagonal uses the literal submask proof for p and v. The three branches exhaust every original 2<=b<=a<d with d+3<=c and feed the same actual natural-label physical consumer."))), []));
}
