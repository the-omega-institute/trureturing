using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper;
internal sealed class ArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform seam and peak bounds on the upper cone", H("Exact physical arithmetic"),
        Blocks(Paragraph(Text("For a>s put h=2^(a-s)>=2,q=2^s>=4,N=hq^4-1. All quantities below are doubled. In terminal order X,U,V,W the old positive masses are h(q-1)M,(q-2)A,(q-2)B,(q-2)L+(h-2)M. The new masses are h(q-1)M',(q-2)2A,(q-2)B'+2A,(q-2)L'+(h-2)M'. Adding the corresponding successor-minus-modulus terminal gives each seam. The old cap is N-1 and the new cap is 2N. Every seam is nonnegative and each preceding peak is at most its cap. Substitution h=u+2,q=v+4 gives nonnegative integer polynomial coefficients for all sixteen inequalities. When a=s use native order U,V,W,X and put the ear before U's terminal. Its old seams vanish; the new seams are A-1,A-1-q,q^3,0, and its doubled peak slacks are 0,q,q^2+q,A-1."))), []));
}
